#!/usr/bin/env python3
"""Source-bound packed table candidates using ordinary knowledge equations.

All actions are translated and proved against the fixed source projection.
Emitters see literal definitions, with no layout selection or new Ink syntax.
"""
import argparse, json, sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, identity
from ink_knowledge.store import entry, read
from producers.representations import refs, REP, MATH
from producers.action_replacement import var, call, cons, convert, trans
from producers.point_delta import match, sub, lift
from producers.equational import Tactic, factor
from producers.packed_tables import build


def generate(model, directory, width=4, hot_keys=(), compiler=None):
    objects=dict(model['objects'])
    def add(decl):
        body=next(iter(decl.values()));deps=refs(decl)
        if 'Datatype' not in decl:
            deps|={i for i,x in objects.items() if 'Datatype' in x['payload'].get('declaration',{})}
        e=entry('theorem' if 'Theorem' in decl else 'definition',MATH,{'declaration':decl},deps,
                parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]))
        i=identity(e);objects[i]=e;return i
    def fun(params,result,body):return add({'Function':dict(params=params,result=result,body=body,recursive=None)})
    def theorem(params,a,z,proof):return add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
    def induction(variable,a,z,bindings,proof):return {'Induction':dict(variable=variable,**{'from':a,'to':z},cases=[dict(bindings=bindings,proof=proof)])}
    layouts={t['datatype']:build(t,objects,add,width) for t in model['tables']}
    if hot_keys:
        from producers.indexed_tables import build as index
        from producers.scalar_equality import word_equality
        from producers.workspace import compiler_path
        equality=word_equality(add,compiler or compiler_path())
        layouts={t['datatype']:index(t,layouts[t['datatype']],objects,add,hot_keys,equality) for t in model['tables']}
    L={'Data':model['state']}
    fields=objects[model['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields']
    if any(f.get('Data') not in layouts for f in fields):raise ValueError('packed producer requires table roots')
    physical=add({'Datatype':dict(constructors=[dict(name='PackedState',fields=[{'Data':layouts[f['Data']]['datatype']} for f in fields])])})
    P={'Data':physical};names=['packed_root_'+str(i) for i in range(len(fields))]
    bound=cons(physical,0,[var(n) for n in names])
    logical_bound=cons(model['state'],0,[call(layouts[f['Data']]['decode'],[var(n)]) for n,f in zip(names,fields)])
    encode=fun([['logical',L]],P,match(var('logical'),[(names,cons(physical,0,[call(layouts[f['Data']]['encode'],[var(n)]) for n,f in zip(names,fields)]))]))
    decode=fun([['physical',P]],L,match(var('physical'),[(names,logical_bound)]))
    fresh=fun([['physical',P]],P,match(var('physical'),[(names,cons(physical,0,[call(layouts[f['Data']]['fresh'],[var(n)]) for n,f in zip(names,fields)]))])) if hot_keys else None
    freshly=lambda p:call(fresh,[p]) if fresh else p
    a=call(decode,[call(encode,[var('logical')])]);z=var('logical')
    rt=theorem([['logical',L]],a,z,induction('logical',a,z,names,
        {'Construct':dict(datatype=model['state'],constructor=0,arguments=[{'Use':dict(theorem=layouts[f['Data']]['roundtrip'],arguments=[var(n)],premises=[])} for n,f in zip(names,fields)])}))
    left=fun([['physical',P],['logical',L]],L,call(decode,[var('physical')]))
    right=fun([['physical',P],['logical',L]],L,var('logical'))
    fresh_left=fun([['physical',P],['logical',L]],P,freshly(var('physical'))) if hot_keys else None
    fresh_right=fun([['physical',P],['logical',L]],P,var('physical')) if hot_keys else None
    freshness_rules=[i for l in layouts.values() for i in l.get('fresh_laws',[])]
    table_operations={t[op]:(t,op) for t in model['tables'] for op in ['get','contains','insert','remove','replace']}
    actions={};all_rules=[law for l in layouts.values() for law in l['laws'].values()]+freshness_rules
    for name,action in model['actions'].items():
        source_obs=action['result']['Data'];constructors=objects[source_obs]['payload']['declaration']['Datatype']['constructors']
        observed=add({'Datatype':dict(constructors=[dict(name=c['name'],fields=[P if f==L else f for f in c['fields']]) for c in constructors])})
        O={'Data':observed}
        roots=dict(zip(action['case']['bindings'],fields))
        renamed=dict(zip(action['case']['bindings'],names))
        def translate(t):
            if 'Var' in t:
                n=t['Var'];return var(renamed.get(n,n)), {'Data':layouts[roots[n]['Data']]['datatype']} if n in roots else None
            if 'Construct' in t:
                x=t['Construct'];d=x['datatype'];args=[translate(a)[0] for a in x['arguments']]
                if d==model['state']:
                    if x['arguments']==[var(n) for n in action['case']['bindings']]:return var('physical'),P
                    return cons(physical,x['constructor'],args),P
                if d==source_obs:return cons(observed,x['constructor'],args),O
                if d in layouts:
                    l=layouts[d]
                    return (cons(l['datatype'],0,[]) if x['constructor']==0 else call(l['push'],args)),{'Data':l['datatype']}
                return cons(d,x['constructor'],args),{'Data':d}
            if 'Call' in t:
                x=t['Call'];f=x['function'];arguments=[translate(a) for a in x['arguments']]
                if f in table_operations:
                    table,op=table_operations[f];l=layouts[table['datatype']]
                    return call(l['functions'][op],[a for a,_ in arguments]), {'Data':l['datatype']} if op in ['insert','remove','replace'] else None
                decl=objects[f]['payload']['declaration']['Function'];args=[]
                for (a,actual),(_,expected) in zip(arguments,decl['params']):
                    if isinstance(expected,dict) and expected.get('Data') in layouts and actual=={'Data':layouts[expected['Data']]['datatype']}:
                        a=call(layouts[expected['Data']]['decode'],[a])
                    args.append(a)
                if isinstance(decl['result'],dict) and decl['result'].get('Data') in layouts:raise ValueError('unsupported table-returning helper; retain direct candidate')
                return call(f,args),decl['result']
            if 'If' in t:
                x=t['If'];a,sort=translate(x['on_true']);b,_=translate(x['on_false'])
                return {'If':dict(condition=translate(x['condition'])[0],on_true=a,on_false=b)},sort
            if 'Binary' in t:
                x=t['Binary'];return {'Binary':dict(op=x['op'],left=translate(x['left'])[0],right=translate(x['right'])[0])},None
            if 'Match' in t:
                x=t['Match'];scrutinee,sort=translate(x['scrutinee'])
                if sort in [{'Data':l['datatype']} for l in layouts.values()]:raise ValueError('unsupported direct table match; retain direct candidate')
                return match(scrutinee,[(b['bindings'],translate(b['body'])[0]) for b in x['branches']]),None
            return t,None
        normal,_=translate(action['case']['normal'])
        rest=action['params'][1:];args=[var(n) for n,_ in rest]
        execute=fun([['physical',P],*rest],O,match(var('physical'),[(names,normal)]))
        onames=['packed_reply','packed_committed','packed_version','packed_post','packed_events']
        hnames=['packed_host','packed_version','packed_post']
        observe=fun([['observation',O]],action['result'],match(var('observation'),[
            (onames,cons(source_obs,0,[var(onames[0]),var(onames[1]),var(onames[2]),call(decode,[var(onames[3])]),var(onames[4])])),
            (hnames,cons(source_obs,1,[var(hnames[0]),var(hnames[1]),call(decode,[var(hnames[2])])]))]))
        nextf=fun([['observation',O]],P,match(var('observation'),[(onames,var(onames[3])),(hnames,var(hnames[2]))]))
        post=fun([['original',action['result']]],L,match(var('original'),[(onames,var(onames[3])),(hnames,var(hnames[2]))]))
        executed=call(execute,[var('physical'),*args]);observed_term=call(observe,[call(execute,[freshly(var('physical')),*args])])
        original=call(action['function'],[call(decode,[var('physical')]),*args])
        case_params=[[n,{'Data':layouts[f['Data']]['datatype']}] for n,f in zip(names,fields)]+rest
        proof=Tactic(objects,all_rules).prove(call(observe,[call(execute,[freshly(bound),*args])]),call(action['function'],[logical_bound,*args]))
        proof=factor(proof,case_params,[],add)
        exact=theorem([['physical',P],*rest],observed_term,original,induction('physical',observed_term,original,names,proof))
        original_logical=call(action['function'],[var('logical'),*args])
        parts=[{'Use':dict(theorem=exact,arguments=[var('physical'),*args],premises=[])},lift({'Hypothesis':0},call(action['function'],[var('delta_hole'),*args]))]
        if hot_keys:parts.insert(0,lift({'Sym':{'Hypothesis':1}},call(observe,[call(execute,[var('delta_hole'),*args])])))
        observation=trans(*parts)
        a=call(decode,[call(nextf,[var('observation')])]);z=call(post,[call(observe,[var('observation')])])
        project=add({'Theorem':dict(params=[['observation',O]],conditions=[],**{'from':a,'to':z},proof={'Induction':dict(variable='observation',**{'from':a,'to':z},cases=[dict(bindings=ns,proof=convert(sub(a,{'observation':cons(observed,i,[var(n) for n in ns])}),sub(z,{'observation':cons(observed,i,[var(n) for n in ns])}))) for i,ns in enumerate([onames,hnames])])})})
        preservation=trans({'Use':dict(theorem=project,arguments=[executed],premises=[])},lift(observation,call(post,[var('delta_hole')])))
        preservation_list=[preservation]
        if hot_keys:
            n=lambda p:call(nextf,[call(execute,[p,*args])])
            a=freshly(n(freshly(var('physical'))));z=n(freshly(var('physical')))
            p=Tactic(objects,all_rules).prove(freshly(n(freshly(bound))),n(freshly(bound)))
            p=factor(p,case_params,[],add)
            maintains=theorem([['physical',P],*rest],a,z,induction('physical',a,z,names,p))
            preservation_list.append(trans(lift({'Sym':{'Hypothesis':1}},freshly(n(var('delta_hole')))),{'Use':dict(theorem=maintains,arguments=[var('physical'),*args],premises=[])},lift({'Hypothesis':1},n(var('delta_hole')))))
        actions[name]=dict(execute=execute,result=O,next=nextf,observe=observe,preservation=preservation_list,observation=observation)
    plan=dict(source_objects=sorted(model['objects']),logical_state=L,physical_state=P,encode=encode,decode=decode,
              relations=[dict(left=left,right=right)],initialisation=[{'Use':dict(theorem=rt,arguments=[var('logical')],premises=[])}],snapshot={'Hypothesis':0},actions=actions)
    if hot_keys:
        a=freshly(call(encode,[var('logical')]));z=call(encode,[var('logical')])
        encoded_bound=cons(model['state'],0,[var(n) for n in names])
        initial=theorem([['logical',L]],a,z,induction('logical',a,z,names,convert(freshly(call(encode,[encoded_bound])),call(encode,[encoded_bound]))))
        plan['relations'].append(dict(left=fresh_left,right=fresh_right));plan['initialisation'].append({'Use':dict(theorem=initial,arguments=[var('logical')],premises=[])})
    e=entry('representation',REP,plan,refs(plan),parameters={'logical':L},result=P,effects=['source-transitions']);e['interface']['operations']=sorted(actions)
    rid=identity(e);objects[rid]=e
    store=Store.publish(directory,objects.values(),{'representations/packed-'+str(width):rid})
    request=dict(schema=1,semantics=REP,input_core_sha256=model['source'],knowledge=store.bundle([rid]),representation=rid)
    return dict(request=request,layouts=layouts,width=width)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('model',type=Path);p.add_argument('-o',type=Path,required=True);p.add_argument('--width',type=int,default=4);p.add_argument('--hot-key',type=int,action='append',default=[]);p.add_argument('--compiler',type=Path)
    a=p.parse_args();a.o.parent.mkdir(parents=True,exist_ok=True);result=generate(read(a.model),a.o.parent/'database',a.width,a.hot_key,a.compiler)
    a.o.write_text(json.dumps(result['request'],separators=(',',':'))+'\n')
if __name__=='__main__':main()
