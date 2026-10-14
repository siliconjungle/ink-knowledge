#!/usr/bin/env python3
"""Author checked standalone result projections in the knowledge database.

The core fixes which observations are public. This producer only proposes literal
bodies that avoid constructing the unused logical state, plus ordinary equalities.
"""
import argparse,copy,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,identity
from ink_knowledge.store import entry
from producers.representations import refs
from producers.action_replacement import var,call,cons,trans,convert
from producers.point_delta import sub,match,free_variables,binding_names
from producers.tree_proofs import Tactic

def projection(term,datatype):
    return match(term,[(['compact_reply','compact_commit','compact_version','compact_rows','compact_events'],cons(datatype,0,[var(n)for n in ['compact_reply','compact_commit','compact_version','compact_events']])),(['compact_host','compact_version','compact_rows'],cons(datatype,1,[var('compact_host'),var('compact_version')]))])

def hygienic_body(term,parameters):
    """Preserve lexical bindings when observers are inlined across components."""
    occupied=set(parameters)
    def reserve(value):
        if isinstance(value,dict):
            if 'Var'in value:occupied.add(value['Var'])
            for child in value.values():reserve(child)
        elif isinstance(value,list):
            for child in value:reserve(child)
        elif isinstance(value,str):occupied.add(value)
    reserve(term)
    serial=0
    def walk(value,scope):
        nonlocal serial
        if isinstance(value,list):return [walk(v,scope)for v in value]
        if not isinstance(value,dict):return value
        if 'Var'in value:return var(scope.get(value['Var'],value['Var']))
        if 'Match'in value:
            node=value['Match'];branches=[]
            for branch in node['branches']:
                local=dict(scope);bindings=[]
                for name in branch['bindings']:
                    fresh=name
                    if fresh in local.values():
                        while True:
                            fresh=name[:40]+'_compact_'+str(serial);serial+=1
                            if fresh not in occupied:break
                        occupied.add(fresh)
                    local[name]=fresh;bindings.append(fresh)
                branches.append(dict(bindings=bindings,body=walk(branch['body'],local)))
            return {'Match':dict(scrutinee=walk(node['scrutinee'],scope),branches=branches)}
        return {k:walk(v,scope)for k,v in value.items()}
    return walk(term,{name:name for name in parameters})

def attach(request,directory):
    request=copy.deepcopy(request);objects=request['knowledge']['objects'];old=request['representation'];plan=objects[old]['payload'];carriers=[i for i,o in objects.items()if 'Datatype'in o.get('payload',{}).get('declaration',{})]
    def add(declaration):
        body=next(iter(declaration.values()));deps=refs(declaration)
        if 'Datatype'not in declaration:deps|=set(carriers)
        obj=entry('theorem'if'Theorem'in declaration else'definition','first-order-inductive-equality-v1',{'declaration':declaration},deps,parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]))
        key=identity(obj);objects[key]=obj
        if 'Datatype'in declaration:carriers.append(key)
        return key
    def projected_body(t,datatype,depth=0):
        if depth>64:raise ValueError('compact authoring depth limit')
        if 'Construct'in t:
            x=t['Construct'];indices=[0,1,2,4]if x['constructor']==0 else[0,1]
            if len(x['arguments'])!=(5 if x['constructor']==0 else 3):raise ValueError('compact source result shape')
            return cons(datatype,x['constructor'],[x['arguments'][i]for i in indices])
        if 'Match'in t:
            x=t['Match'];return match(x['scrutinee'],[(b['bindings'],projected_body(b['body'],datatype,depth+1))for b in x['branches']])
        if 'If'in t:
            x=t['If'];return {'If':{**x,**{k:projected_body(x[k],datatype,depth+1)for k in ['on_true','on_false']}}}
        if 'Var'in t:return projection(t,datatype)
        if 'Call'in t:
            x=t['Call'];f=objects[x['function']]['payload']['declaration']['Function']
            if f['recursive']is not None:raise ValueError('recursive observer needs an authored projection lemma')
            return projected_body(sub(f['body'],dict(zip([n for n,_ in f['params']],x['arguments']))),datatype,depth+1)
        raise ValueError('unsupported observer projection '+str(t)[:160])
    names={}
    for name,action in plan['actions'].items():
        observation=objects[action['observe']]['payload']['declaration']['Function']
        constructors=objects[observation['result']['Data']]['payload']['declaration']['Datatype']['constructors']
        dtype=add({'Datatype':{'constructors':[dict(name=c['name'],fields=[c['fields'][i]for i in ([0,1,2,4]if tag==0 else[0,1])])for tag,c in enumerate(constructors)]}})
        result=var('execution_result');original=call(action['observe'],[result]);params=[['execution_result',action['result']]]
        body=projected_body(sub(observation['body'],{observation['params'][0][0]:result}),dtype)
        body=hygienic_body(body,[name for name,_ in params])
        observe=add({'Function':dict(params=params,result={'Data':dtype},recursive=None,body=body)})
        tactic=Tactic(objects,add)
        left,right=call(observe,[result]),projection(original,dtype)
        # A direct result projection needs only exhaustive constructor cases.
        # The general tactic retains intermediate normalisation proofs, which
        # duplicate large decoded states even though those fields are discarded.
        # Try small Convert leaves first; ordinary checking remains authority.
        input_type=action['result']['Data']
        input_constructors=objects[input_type]['payload']['declaration']['Datatype']['constructors']
        cases=[];occupied=free_variables([left,right])|binding_names([left,right])
        for tag,constructor in enumerate(input_constructors):
            bindings=[]
            for index,_ in enumerate(constructor['fields']):
                fresh='compact_case_'+str(tag)+'_'+str(index)
                while fresh in occupied:fresh+='_'
                occupied.add(fresh);bindings.append(fresh)
            value=cons(input_type,tag,[var(n)for n in bindings])
            a,z=sub(left,{'execution_result':value}),sub(right,{'execution_result':value})
            env={n:({'Data':input_type}if t=='SelfType'else t)for n,t in zip(bindings,constructor['fields'])}
            if tactic.normal(a,env)!=tactic.normal(z,env):break
            cases.append(dict(bindings=bindings,proof=convert(a,z)))
        if len(cases)==len(input_constructors):
            lemma=add({'Theorem':dict(params=params,conditions=[],**{'from':left,'to':right},
                proof={'Cases':dict(variable='execution_result',**{'from':left,'to':right},cases=cases)})})
        else:
            lemma=tactic.theorem('compact-'+name,params,left,right)
        execute=objects[action['execute']]['payload']['declaration']['Function'];executed=call(action['execute'],[var(n)for n,_ in execute['params']])
        # Representation obligations fix physical/logical parameter spellings.
        executed['Call']['arguments'][0]=var('physical')
        proof=trans({'Use':dict(theorem=lemma,arguments=[executed],premises=[])},{'Substitute':dict(variable='compact_hole',context=projection(var('compact_hole'),dtype),equality=action['observation'])})
        action['compact']=dict(observe=observe,result={'Data':dtype},proof=proof)
        names[name]=lemma
    obj=copy.deepcopy(objects[old]);obj['payload']=plan;obj['dependencies']=sorted(refs(plan));new=identity(obj);objects[new]=obj
    # Wide proof closures need small authenticated leaves: each included entry
    # carries its membership witness, so repeating 64-entry leaves can dominate
    # transport size. This changes neither object identities nor proof admission.
    store=Store.publish(directory,list(objects.values()),names,leaf_size=2 if len(objects)>64 else 64)
    request['representation']=new;request['knowledge']=store.bundle([new])
    return request

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('request',type=Path);p.add_argument('--store',type=Path,required=True);p.add_argument('-o','--output',type=Path,required=True);a=p.parse_args()
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(attach(json.loads(a.request.read_text()),a.store),separators=(',',':'))+'\n')
