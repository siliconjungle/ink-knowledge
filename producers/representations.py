#!/usr/bin/env python3
"""Untrusted source-bound physical layouts and migration proposals.

No producer is correctness authority. All universal equations are rechecked.
An optional checked action-replacement proposal supplies faster action bodies.
"""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,identity
from ink_knowledge.store import entry,read
from action_replacement import var,call,cons,convert,trans
MATH='first-order-inductive-equality-v1'
REP='ink-source-representation-v1'
MIG='ink-representation-migration-v1'
def refs(x):
    if isinstance(x,str):return {x} if len(x)==64 and all(c in '0123456789abcdef' for c in x) else set()
    if isinstance(x,dict):return set().union(*(refs(v) for v in x.values())) if x else set()
    if isinstance(x,list):return set().union(*(refs(v) for v in x)) if x else set()
    return set()
def match(x,branches):return {'Match':dict(scrutinee=x,branches=[dict(bindings=ns,body=t) for ns,t in branches])}
def subst(proof,context):return {'Substitute':dict(variable='replacement',context=context,equality=proof)}
def generate(model,directory,replacement=None,cache_query=None):
    objects=dict(model['objects']);L={'Data':model['state']}
    if replacement:
        if replacement['input_core_sha256']!=model['source']:raise ValueError('replacement source mismatch')
        objects.update(replacement['knowledge']['objects'])
        # The selected model must be supplied alongside its whole-action proofs.
        selected=replacement['selected_model']
    else:selected=model
    def add(decl,extra=()):
        payload={'declaration':decl};body=next(iter(decl.values()))
        e=entry('theorem' if 'Theorem' in decl else 'definition',MATH,payload,refs(payload)|set(extra),parameters=dict(body.get('params',[])),result=body.get('result'))
        i=identity(e);objects[i]=e;return i
    def fun(params,result,body):return add({'Function':dict(params=params,result=result,body=body,recursive=None)})
    requests=[];plans=[];ids=[]
    # Two genuinely different tuple layouts, chosen entirely by this database
    # producer. Neither the core nor the native emitter recognises their shape.
    fields=model['objects'][model['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields']
    for reverse in [False,True]:
        order=list(range(len(fields)));order=order[::-1] if reverse else order
        # The second physical layout has a redundant validity field. It can be
        # replaced with any database-defined maintained view with the same proofs.
        cache=model['actions'][cache_query] if reverse and cache_query else None
        if cache and (len(cache['params'])!=2 or cache['case']['normal'].get('Construct',{}).get('constructor')!=0 or cache['case']['normal']['Construct']['arguments'][1]!={'Bool':False}):raise ValueError('producer supports a parameterless query with a direct reply')
        cache_sort=model['objects'][cache['result']['Data']]['payload']['declaration']['Datatype']['constructors'][0]['fields'][0] if cache else None
        Pid=add({'Datatype':dict(constructors=[dict(name='Reversed' if reverse else 'Direct',fields=[fields[i] for i in order]+([cache_sort] if cache else ['Bool'] if reverse else []))])})
        P={'Data':Pid};names=['root_'+str(i) for i in range(len(fields))]
        cache_body=substitute_names(cache['case']['normal']['Construct']['arguments'][0],dict(zip(cache['case']['bindings'],names))) if cache else None
        physical=lambda xs:cons(Pid,0,[xs[i] for i in order]+([cache_body] if cache else [{'Bool':True}] if reverse else []))
        encode=fun([['logical',L]],P,match(var('logical'),[(names,physical([var(n) for n in names]))]))
        pnames=[names[i] for i in order]+(['cached_reply'] if cache else ['valid'] if reverse else [])
        decode=fun([['physical',P]],L,match(var('physical'),[(pnames,cons(model['state'],0,[var(n) for n in names]))]))
        lhs=call(decode,[call(encode,[var('logical')])]);rhs=var('logical')
        roundtrip=add({'Theorem':dict(params=[['logical',L]],conditions=[],**{'from':lhs,'to':rhs},proof={'Induction':dict(variable='logical',**{'from':lhs,'to':rhs},cases=[dict(bindings=names,proof=convert(call(decode,[call(encode,[cons(model['state'],0,[var(n) for n in names])])]),cons(model['state'],0,[var(n) for n in names])))])})})
        left=fun([['physical',P],['logical',L]],P,var('physical'))
        right=fun([['physical',P],['logical',L]],P,call(encode,[var('logical')]))
        relation=lambda p,l:(call(left,[p,l]),call(right,[p,l]))
        # Relation is physical = encode(logical); use the hypothesis through
        # decode, then the generic round-trip theorem.
        eq={'Hypothesis':0}
        snapshot=trans(convert(call(decode,[var('physical')]),call(decode,[relation(var('physical'),var('logical'))[0]])),subst(eq,call(decode,[var('replacement')])),convert(call(decode,[relation(var('physical'),var('logical'))[1]]),lhs),{'Use':dict(theorem=roundtrip,arguments=[var('logical')],premises=[])})
        actions={}
        for name,a in model['actions'].items():
            sa=selected['actions'][name];rest=a['params'][1:];params=[['initial',P]]+rest
            args=[var(n) for n,_ in rest]
            post=lambda o:match(o,[(['post_reply','post_committed','post_version','post_rows','post_events'],var('post_rows')),(['post_host','post_version','post_rows'],var('post_rows'))])
            result=a['result']
            if cache and name==cache_query:
                obsid=a['result']['Data'];normal=cache['case']['normal']['Construct']['arguments']
                pair=add({'Datatype':dict(constructors=[dict(name='RetainedQuery',fields=[P,a['result']])])});result={'Data':pair}
                reply=cons(obsid,0,[var('cached_reply'),{'Bool':False},var('version'),cons(model['state'],0,[var(n) for n in names]),normal[4]])
                body=match(var('initial'),[(pnames,cons(pair,0,[var('initial'),reply]))])
                execute=fun(params,result,body)
                observe=fun([['observation',result]],a['result'],match(var('observation'),[(['retained','reply_value'],var('reply_value'))]))
                nextf=fun([['observation',result]],P,match(var('observation'),[(['retained','reply_value'],var('retained'))]))
            else:
                execute=fun(params,result,call(sa['function'],[call(decode,[var('initial')])]+args))
                observe=fun([['observation',result]],a['result'],var('observation'))
                nextf=fun([['observation',result]],P,call(encode,[post(var('observation'))]))
            executed=call(execute,[var('physical')]+args);observed=call(observe,[executed]);original=call(a['function'],[var('logical')]+args)
            same=call(sa['function'],[var('logical')]+args)
            if cache and name==cache_query:
                bound=cons(model['state'],0,[var(n) for n in names]);start=call(observe,[call(execute,[call(encode,[var('logical')])]+args)])
                equality=add({'Theorem':dict(params=[['logical',L]]+rest,conditions=[],**{'from':start,'to':same},proof={'Induction':dict(variable='logical',**{'from':start,'to':same},cases=[dict(bindings=names,proof=convert(call(observe,[call(execute,[call(encode,[bound])]+args)]),call(sa['function'],[bound]+args)))])})})
                observation=trans(convert(observed,call(observe,[call(execute,[relation(var('physical'),var('logical'))[0]]+args)])),subst(eq,call(observe,[call(execute,[var('replacement')]+args)])),convert(call(observe,[call(execute,[relation(var('physical'),var('logical'))[1]]+args)]),start),{'Use':dict(theorem=equality,arguments=[var('logical')]+args,premises=[])})
            else:observation=trans(convert(observed,call(sa['function'],[call(decode,[var('physical')])]+args)),subst(snapshot,call(sa['function'],[var('replacement')]+args)))
            if replacement:
                # Existing whole-action proof states original == selected.
                actionproof=replacement['action_replacement']['proofs'][name]
                bound_args=[var(n) for n,_ in a['params']]
                law=add({'Theorem':dict(params=a['params'],conditions=[],**{'from':call(a['function'],bound_args),'to':call(sa['function'],bound_args)},proof=actionproof)})
                observation=trans(observation,{'Sym':{'Use':dict(theorem=law,arguments=[var('logical')]+args,premises=[])}})
            else:observation=trans(observation,convert(same,original))
            before,after=relation(call(nextf,[executed]),post(original))
            context=call(encode,[post(var('replacement'))])
            if cache and name==cache_query:
                retained=call(nextf,[executed]);pbound=cons(Pid,0,[var(n) for n in pnames])
                retention=add({'Theorem':dict(params=[['physical',P]]+rest,conditions=[],**{'from':retained,'to':var('physical')},proof={'Induction':dict(variable='physical',**{'from':retained,'to':var('physical')},cases=[dict(bindings=pnames,proof=convert(call(nextf,[call(execute,[pbound]+args)]),pbound))])})})
                state_eq=add({'Theorem':dict(params=[['logical',L]]+rest,conditions=[],**{'from':post(original),'to':var('logical')},proof={'Induction':dict(variable='logical',**{'from':post(original),'to':var('logical')},cases=[dict(bindings=names,proof=convert(post(call(a['function'],[bound]+args)),bound))])})},[a['result']['Data']])
                equality={'Use':dict(theorem=state_eq,arguments=[var('logical')]+args,premises=[])}
                preservation=trans(convert(before,retained),{'Use':dict(theorem=retention,arguments=[var('physical')]+args,premises=[])},convert(var('physical'),relation(var('physical'),var('logical'))[0]),eq,convert(relation(var('physical'),var('logical'))[1],call(encode,[var('logical')])),{'Sym':subst(equality,call(encode,[var('replacement')]))},convert(call(encode,[post(original)]),after))
            else:preservation=trans(convert(before,call(encode,[post(observed)])),subst(observation,context),convert(call(encode,[post(original)]),after))
            actions[name]=dict(execute=execute,result=result,next=nextf,observe=observe,preservation=[preservation],observation=observation)
        init_a,init_z=relation(call(encode,[var('logical')]),var('logical'))
        plan=dict(source_objects=sorted(model["objects"]),logical_state=L,physical_state=P,encode=encode,decode=decode,relations=[dict(left=left,right=right)],initialisation=[convert(init_a,init_z)],snapshot=snapshot,actions=actions)
        e=entry('representation',REP,plan,refs(plan),parameters={'logical':L},result=P,effects=['source-transitions']);e['interface']['operations']=sorted(actions)
        rid=identity(e);objects[rid]=e;plans.append(plan);ids.append(rid)
    old,new=plans
    migrate=fun([['physical',old['physical_state']]],new['physical_state'],call(new['encode'],[call(old['decode'],[var('physical')])]))
    r=new['relations'][0];a=call(r['left'],[call(migrate,[var('physical')]),var('logical')]);z=call(r['right'],[call(migrate,[var('physical')]),var('logical')])
    proof=trans(convert(a,call(new['encode'],[call(old['decode'],[var('physical')])])),subst(old['snapshot'],call(new['encode'],[var('replacement')])),convert(call(new['encode'],[var('logical')]),z))
    migration=dict(**{'from':ids[0],'to':ids[1]},function=migrate,preservation=[proof]);e=entry('bridge',MIG,migration,refs(migration));e['interface']['operations']=['migrate'];mid=identity(e);objects[mid]=e
    store=Store.publish(directory,list(objects.values()),{'representations/direct':ids[0],'representations/reversed':ids[1],'migrations/direct-to-reversed':mid})
    for rid in ids:
        requests.append(dict(schema=1,semantics=REP,input_core_sha256=model['source'],knowledge=store.bundle([rid]),representation=rid))
    return dict(requests=requests,migration=dict(root=mid,knowledge=store.bundle([mid,*objects])))
def substitute_names(x,mapping):
    if isinstance(x,dict):
        if set(x)=={'Var'}:return var(mapping.get(x['Var'],x['Var']))
        return {k:substitute_names(v,mapping) for k,v in x.items()}
    if isinstance(x,list):return [substitute_names(v,mapping) for v in x]
    # Induction variable names/binders require renaming too.
    if isinstance(x,str):return mapping.get(x,x)
    return x
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('model',type=Path);p.add_argument('-o','--output',type=Path,required=True);p.add_argument('--replacement',type=Path);p.add_argument('--selected-model',type=Path);p.add_argument('--cache-query')
    a=p.parse_args();a.output.parent.mkdir(parents=True,exist_ok=True)
    replacement=read(a.replacement) if a.replacement else None
    if replacement:replacement['selected_model']=read(a.selected_model)
    result=generate(read(a.model),a.output.parent/'database',replacement,a.cache_query);a.output.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
