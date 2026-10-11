#!/usr/bin/env python3
"""Close group-delta interpretations and bind them to a parameterised source query.

The example uses the row value as its group. Every key, query value, row order
and duplicate multiplicity is covered; no reachable-state uniqueness assumption.
"""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]));sys.path.insert(0,str(Path(__file__).resolve().parent))
from ink_knowledge import Store
from producers.state_calculus import build,CanonicalLibrary
from producers.general_laws import var,call,construct,refl,trans,congruence
from producers.point_delta import sub,normal,equality,binary,choice,lift
from producers.action_replacement import convert

def generate(model,directory):
    lib=build(CanonicalLibrary());n=lib.names;objects=lib.objects;objects.update(model['objects'])
    table=model['tables'][0];action=model['actions']['total'];query=action['case']['normal']['Construct']['arguments'][0]
    binding=action['case']['bindings'][0];argument=action['params'][-1][0];RS={'Data':table['datatype']}
    carriers=[i for i,e in model['objects'].items()if 'Datatype'in e['payload'].get('declaration',{})]
    concrete={n['AggregateRows']:table['datatype'],n['group_source_remove']:table['remove'],n['group_source_replace']:table['replace']}
    contribution=lib.function('source_group_contribution',[['value','U64'],['query','U64']],'U64',choice(binary('==',var('value'),var('query')),var('value'),{'U64':0}))
    sorts={n['AggregateRow']:'U64'};functions={n['group_contribution']:dict(params=['value','query'],body=objects[contribution]['payload']['declaration']['Function']['body'])}
    def sort(s):return sorts.get(s.get('Data'),{'Data':concrete.get(s.get('Data'),s.get('Data'))})if isinstance(s,dict)and 'Data'in s else s
    def term(t):
        if isinstance(t,list):return[term(x)for x in t]
        if not isinstance(t,dict):return t
        if 'Data'in t:return sort(t)
        if 'Call'in t and t['Call']['function']in functions:
            lam=functions[t['Call']['function']];return sub(lam['body'],dict(zip(lam['params'],[term(a)for a in t['Call']['arguments']])))
        return {k:(concrete.get(v,v)if k in ('function','datatype')else term(v))for k,v in t.items()}
    for name in ('group_total','group_delta_remove','group_delta_replace'):
        old=n[name];d=objects[old]['payload']['declaration']['Function'];actual={**d,'params':[[p,sort(s)]for p,s in d['params']],'result':sort(d['result']),'body':term(d['body'])}
        concrete[old]=lib.store('source_'+name,'Function',actual,extra=carriers)
    r,k,q,new=map(var,('rows','key','query','new'));T=lambda r:call(concrete[n['group_total']],r,q)
    source=lambda r:sub(query,{binding:r,argument:q})
    nil=construct(table['datatype'],0);head,value,tail=map(var,('head','value','tail'));bound=construct(table['datatype'],1,head,value,tail);guard=binary('==',value,q)
    branches={}
    for flag in (False,True):
        facts=[(guard,{'Bool':flag},1)];left,right=normal(source(bound),objects),normal(T(bound),objects)
        # The false branch contributes zero; discharge its exact word identity.
        if not flag:
            proof=trans(equality(source(bound),source(tail),objects,facts=facts),{'Hypothesis':0},{'Sym':trans(equality(T(bound),binary('+',{'U64':0},T(tail)),objects,facts=facts),{'Use':dict(theorem=n['group_word_left_zero'],arguments=[T(tail)],premises=[])})})
        else:proof=equality(source(bound),T(bound),objects,(source(tail),T(tail),0),facts)
        branches['on_true'if flag else'on_false']=proof
    correspondence=lib.theorem('source_group_query_exact',[['rows',RS],['query','U64']],source(r),T(r),{'Induction':dict(variable='rows',**{'from':source(r),'to':T(r)},cases=[dict(bindings=[],proof=convert(source(nil),T(nil))),dict(bindings=['head','value','tail'],proof={'BoolSplit':dict(condition=guard,**{'from':source(bound),'to':T(bound)},**branches)})])},extra=carriers)
    roots=[correspondence]
    for operation in ('remove','replace'):
        args=[r,k]+([new]if operation=='replace'else[]);updated=call(table[operation],*args)
        delta=call(concrete[n['group_delta_'+operation]],r,k,q,*([new]if operation=='replace'else[]))
        middle=binary('+',T(r),delta);result=binary('+',source(r),delta)
        instance={'Instance':dict(theorem=n['group_'+operation+'_repair_exact'],sorts=sorts,functions=functions,definitions=concrete,assumptions={},arguments=[r,k,q]+([new]if operation=='replace'else[]),premises=[])}
        proof=trans({'Use':dict(theorem=correspondence,arguments=[updated,q],premises=[])},instance,{'Sym':lift({'Use':dict(theorem=correspondence,arguments=[r,q],premises=[])},binary('+',var('delta_hole'),delta))})
        roots.append(lib.theorem('source_group_'+operation+'_repair_exact',[['rows',RS],['key','U64'],['query','U64']]+([['new','U64']]if operation=='replace'else[]),source(updated),result,proof,extra=[*carriers,*concrete,*concrete.values(),*functions,*sorts,contribution]))
    store=Store.publish(directory,objects.values(),lib.names);return store.bundle(roots)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('model',type=Path);p.add_argument('-o',type=Path,required=True);a=p.parse_args();a.o.parent.mkdir(parents=True,exist_ok=True);view=generate(json.loads(a.model.read_text()),a.o.parent/'grouped-database');a.o.write_text(json.dumps(view,separators=(',',':'))+'\n');print(json.dumps(dict(status='proposed',roots=view['roots'])))
if __name__=='__main__':main()
