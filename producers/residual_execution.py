#!/usr/bin/env python3
"""Database-authored smaller private execution carriers, with full contracts.

The discarded logical state is reconstructed only by the full observer. Next
state, complete observation and compact observation all retain ordinary proofs.
The backend receives literal functions and performs no envelope transformation.
"""
import argparse,copy,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,identity,canonical
from ink_knowledge.store import entry
from producers.representations import refs
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import normal,match,lift
from producers.compact_observation import projection
from producers.tree_proofs import Tactic

def post(observation):
    return match(observation,[(['res_reply','res_commit','res_version','res_rows','res_events'],var('res_rows')),(['res_host','res_version','res_rows'],var('res_rows'))])

def generate(model,request,directory,action=None):
    request=copy.deepcopy(request);objects=request['knowledge']['objects'];old=request['representation'];plan=copy.deepcopy(objects[old]['payload'])
    carriers={i for i,o in objects.items()if 'Datatype'in o['payload'].get('declaration',{})}
    def add(decl):
        body=next(iter(decl.values()));dependencies=refs(decl)
        if 'Datatype'not in decl:dependencies|=carriers
        obj=entry('theorem'if'Theorem'in decl else'definition','first-order-inductive-equality-v1',dict(declaration=decl),dependencies,parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]))
        ident=identity(obj);objects[ident]=obj
        if 'Datatype'in decl:carriers.add(ident)
        return ident
    def fn(params,result,body):return add({'Function':dict(params=params,result=result,body=body,recursive=None)})
    def theorem(params,conditions,a,z,proof):return add({'Theorem':dict(params=params,conditions=conditions,**{'from':a,'to':z},proof=proof)})
    def use(i,args,premises=()):return {'Use':dict(theorem=i,arguments=args,premises=list(premises))}
    P,L=plan['physical_state'],plan['logical_state'];p,l=var('physical'),var('logical')
    relations=lambda p,l:[dict(**{'from':call(r['left'],[p,l]),'to':call(r['right'],[p,l])})for r in plan['relations']]
    conditions=relations(p,l)
    snapshot=theorem([['physical',P],['logical',L]],conditions,call(plan['decode'],[p]),l,plan['snapshot'])
    changed=0
    for name,a in plan['actions'].items():
        if action is not None and name!=action:continue
        if 'compact'not in a:continue
        old_action=copy.deepcopy(a);f=objects[a['execute']]['payload']['declaration']['Function']
        if f['recursive']is not None:continue
        E=a['result'];O=model['actions'][name]['result'];C=a['compact']['result']
        cs=objects[E['Data']]['payload']['declaration']['Datatype']['constructors']
        if len(cs)!=1 or cs[0]['fields']!=[P,O]:continue
        # Guards are themselves checked ordinary equalities, not recognisers.
        bound=cons(E['Data'],0,[var('role_state'),var('role_observation')]);role_params=[['role_state',P],['role_observation',O]]
        theorem(role_params,[],call(a['next'],[bound]),var('role_state'),convert(call(a['next'],[bound]),var('role_state')))
        theorem(role_params,[],call(a['observe'],[bound]),var('role_observation'),convert(call(a['observe'],[bound]),var('role_observation')))
        N=add({'Datatype':dict(constructors=[dict(name='PhysicalAndCompactObservation',fields=[P,C])])})
        def project(t,depth=0):
            if depth>96:raise ValueError('residual observation authoring depth budget')
            if 'Construct'in t:
                x=t['Construct']
                if x['datatype']==O['Data']and x['constructor']in [0,1]:
                    indices=[0,1,2,4]if x['constructor']==0 else[0,1]
                    return cons(C['Data'],x['constructor'],[x['arguments'][i]for i in indices])
            if 'If'in t:return {'If':{**t['If'],**{k:project(t['If'][k],depth+1)for k in ['on_true','on_false']}}}
            if 'Match'in t:return {'Match':dict(scrutinee=t['Match']['scrutinee'],branches=[dict(b,body=project(b['body'],depth+1))for b in t['Match']['branches']])}
            if 'Call'in t:
                x=t['Call'];g=objects[x['function']]['payload']['declaration']['Function']
                if g['recursive']is None:
                    from producers.point_delta import sub
                    return project(sub(g['body'],dict(zip([n for n,_ in g['params']],x['arguments']))),depth+1)
            raise ValueError('observer needs an explicit residual-carrier lemma')
        def reduce(t,depth=0):
            if depth>96:raise ValueError('residual carrier authoring depth budget')
            if 'Construct'in t:
                x=t['Construct']
                if x['datatype']==E['Data']and x['constructor']==0 and len(x['arguments'])==2:
                    return cons(N,0,[x['arguments'][0],project(x['arguments'][1])])
            if 'If'in t:return {'If':{**t['If'],**{k:reduce(t['If'][k],depth+1)for k in ['on_true','on_false']}}}
            if 'Match'in t:
                x=t['Match'];return {'Match':dict(scrutinee=x['scrutinee'],branches=[dict(b,body=reduce(normal(b['body'],objects),depth+1))for b in x['branches']])}
            raise ValueError('execution carrier is not structurally available')
        body=reduce(normal(f['body'],objects));execute=fn(f['params'],{'Data':N},body)
        n=var('execution_result');bindings=['new_state','new_observation'];pair=cons(N,0,[var(x)for x in bindings])
        nxt=fn([['execution_result',{'Data':N}]],P,match(n,[(bindings,var('new_state'))]))
        compact=fn([['execution_result',{'Data':N}]],C,match(n,[(bindings,var('new_observation'))]))
        compact_value,state_value=var('compact_value'),var('state_value')
        merge=fn([['compact_value',C],['state_value',L]],O,match(compact_value,[(['res_reply','res_commit','res_version','res_events'],cons(O['Data'],0,[var('res_reply'),var('res_commit'),var('res_version'),state_value,var('res_events')])),(['res_host','res_version'],cons(O['Data'],1,[var('res_host'),var('res_version'),state_value]))]))
        observe=fn([['execution_result',{'Data':N}]],O,match(n,[(bindings,call(merge,[var('new_observation'),call(plan['decode'],[var('new_state')])]))]))
        tactic=Tactic(objects,add)
        reconstruct=tactic.theorem('residual-reconstruction',[['observation',O]],call(merge,[projection(var('observation'),C['Data']),post(var('observation'))]),var('observation'),induction='observation')
        observation=tactic.theorem('residual-elimination',[['execution_result',{'Data':N}]],call(observe,[n]),call(merge,[call(compact,[n]),call(plan['decode'],[call(nxt,[n])])]),induction='execution_result')
        actual=[p,*[var(n)for n,_ in model['actions'][name]['params'][1:]]]
        old_exec,new_exec=call(old_action['execute'],actual),call(execute,actual)
        old_next,new_next=call(old_action['next'],[old_exec]),call(nxt,[new_exec])
        # These unconditional lemmas establish the private carrier transformation.
        next_lemma=Tactic(objects,add).theorem('residual-next',f['params'],call(nxt,[call(execute,[var(n)for n,_ in f['params']])]),call(old_action['next'],[call(old_action['execute'],[var(n)for n,_ in f['params']])]))
        compact_lemma=Tactic(objects,add).theorem('residual-compact',f['params'],call(compact,[call(execute,[var(n)for n,_ in f['params']])]),projection(call(old_action['observe'],[call(old_action['execute'],[var(n)for n,_ in f['params']])]),C['Data']))
        pa=[['physical',P],['logical',L],*model['actions'][name]['params'][1:]];pa_args=[var(n)for n,_ in pa]
        source=call(model['actions'][name]['function'],[l,*actual[1:]])
        old_observation=theorem(pa,conditions,call(old_action['observe'],[old_exec]),source,old_action['observation'])
        preserves=[theorem(pa,conditions,c['from'],c['to'],proof)for c,proof in zip(relations(old_next,post(source)),old_action['preservation'])]
        premises=[{'Hypothesis':i}for i in range(len(conditions))]
        next_eq=use(next_lemma,actual)
        state_eq=trans(lift(next_eq,call(plan['decode'],[var('delta_hole')])),use(snapshot,[old_next,post(source)],[use(i,pa_args,premises)for i in preserves]))
        compact_eq=trans(use(compact_lemma,actual),lift(use(old_observation,pa_args,premises),projection(var('delta_hole'),C['Data'])))
        full_eq=trans(use(observation,[new_exec]),{'Call':dict(function=merge,arguments=[compact_eq,state_eq])},use(reconstruct,[source]))
        preservation=[]
        for relation,lemma in zip(plan['relations'],preserves):
            left=lift(next_eq,call(relation['left'],[var('delta_hole'),post(source)]))
            right=lift(next_eq,call(relation['right'],[var('delta_hole'),post(source)]))
            preservation.append(trans(left,use(lemma,pa_args,premises),{'Sym':right}))
        a.update(execute=execute,result={'Data':N},next=nxt,observe=observe,observation=full_eq,preservation=preservation,
            compact=dict(result=C,observe=compact,proof=compact_eq));changed+=1
    if not changed:raise ValueError('no compact paired execution carriers')
    obj=copy.deepcopy(objects[old]);obj['payload']=plan;obj['dependencies']=sorted(refs(plan));rid=identity(obj);objects[rid]=obj
    store=Store.publish(directory,objects.values());request['representation']=rid;request['knowledge']=store.bundle([rid]);return request

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('model',type=Path);p.add_argument('request',type=Path);p.add_argument('--store',type=Path,required=True);p.add_argument('-o',type=Path,required=True);a=p.parse_args()
    a.o.write_bytes(canonical(generate(json.loads(a.model.read_bytes()),json.loads(a.request.read_bytes()),a.store))+b'\n')
