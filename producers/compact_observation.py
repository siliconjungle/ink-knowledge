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
from producers.action_replacement import var,call,cons,trans
from producers.point_delta import sub,match
from producers.tree_proofs import Tactic

def projection(term,datatype):
    return match(term,[(['compact_reply','compact_commit','compact_version','compact_rows','compact_events'],cons(datatype,0,[var(n)for n in ['compact_reply','compact_commit','compact_version','compact_events']])),(['compact_host','compact_version','compact_rows'],cons(datatype,1,[var('compact_host'),var('compact_version')]))])

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
        observe=add({'Function':dict(params=params,result={'Data':dtype},recursive=None,body=body)})
        tactic=Tactic(objects,add)
        lemma=tactic.theorem('compact-'+name,params,call(observe,[result]),projection(original,dtype))
        execute=objects[action['execute']]['payload']['declaration']['Function'];executed=call(action['execute'],[var(n)for n,_ in execute['params']])
        # Representation obligations fix physical/logical parameter spellings.
        executed['Call']['arguments'][0]=var('physical')
        proof=trans({'Use':dict(theorem=lemma,arguments=[executed],premises=[])},{'Substitute':dict(variable='compact_hole',context=projection(var('compact_hole'),dtype),equality=action['observation'])})
        action['compact']=dict(observe=observe,result={'Data':dtype},proof=proof)
        names[name]=lemma
    obj=copy.deepcopy(objects[old]);obj['payload']=plan;obj['dependencies']=sorted(refs(plan));new=identity(obj);objects[new]=obj
    store=Store.publish(directory,list(objects.values()),names)
    request['representation']=new;request['knowledge']=store.bundle([new])
    return request

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('request',type=Path);p.add_argument('--store',type=Path,required=True);p.add_argument('-o','--output',type=Path,required=True);a=p.parse_args()
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(attach(json.loads(a.request.read_text()),a.store),separators=(',',':'))+'\n')
