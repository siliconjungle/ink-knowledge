#!/usr/bin/env python3
"""Untrusted product composition of source-bound representation proofs.

Relations and assumptions are retained component by component. A product uses
one observable reply/event stream. Its alternatives still need cost evidence;
composition alone does not imply profitable shared execution.
"""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from ink_knowledge import Store,identity
from ink_knowledge.store import entry
from producers.state_calculus import CanonicalLibrary
from producers.general_laws import var,call,construct,match,hyp,use,trans,substitute,sym
from producers.action_replacement import convert
from producers.representations import refs,unchanged_query

def compose(model,requests,directory,query_providers=None):
    query_providers=query_providers or {}
    if any(k not in model['actions'] or v not in (0,1)or not unchanged_query(model,model['actions'][k])for k,v in query_providers.items()):raise ValueError('query providers require an unchanged source query and a component index')
    if len(requests)!=2:raise ValueError('composition requires two components')
    if any(r['input_core_sha256']!=model['source']for r in requests):raise ValueError('component source mismatch')
    lib=CanonicalLibrary();lib.objects=dict(model['objects']);plans=[]
    for r in requests:
        for i,e in r['knowledge']['objects'].items():
            if i in lib.objects and lib.objects[i]!=e:raise ValueError('conflicting canonical object')
            lib.objects[i]=e
        plans.append(lib.objects[r['representation']]['payload'])
    L={'Data':model['state']}
    if any(p['logical_state']!=L or p['source_objects']!=sorted(model['objects'])for p in plans):raise ValueError('component projection mismatch')
    carriers=lambda:[i for i,e in lib.objects.items()if 'Datatype'in e['payload'].get('declaration',{})]
    def fun(name,params,result,body):return lib.function(name,params,result,body,extra=carriers())
    def theorem(name,params,conditions,a,z,proof):return lib.store(name,'Theorem',dict(params=params,conditions=conditions,**{'from':a,'to':z},proof=proof),extra=carriers())
    pair=lib.store('ProductState','Datatype',dict(constructors=[dict(name='Product',fields=[p['physical_state']for p in plans])]))
    P={'Data':pair};physical=var('physical');logical=var('logical')
    projections=[fun('component_'+str(i),[['physical',P]],p['physical_state'],match(physical,(['left','right'],var('left'if i==0 else'right'))))for i,p in enumerate(plans)]
    component=lambda i:call(projections[i],physical)
    encode=fun('encode',[['logical',L]],P,construct(pair,0,*[call(p['encode'],logical)for p in plans]))
    decode=fun('decode',[['physical',P]],L,call(plans[0]['decode'],component(0)))
    relations=[];conditions=[];offsets=[];init=[]
    for i,p in enumerate(plans):
        offsets.append(len(relations));conditions.append([dict(**{'from':call(r['left'],physical,logical),'to':call(r['right'],physical,logical)})for r in p['relations']])
        for j,r in enumerate(p['relations']):
            lifted={side:fun(f'relation_{i}_{j}_{side}',[['physical',P],['logical',L]],lib.objects[r[side]]['payload']['declaration']['Function']['result'],call(r[side],component(i),logical))for side in ('left','right')}
            relations.append(lifted)
            a,z=(call(r[side],call(p['encode'],logical),logical)for side in ('left','right'))
            lemma=theorem(f'initial_{i}_{j}',[['logical',L]],[],a,z,p['initialisation'][j]);init.append(use(lemma,logical))
    assumptions=lambda i:[hyp(offsets[i]+j)for j in range(len(plans[i]['relations']))]
    use_with=lambda lemma,i,args:{'Use':dict(theorem=lemma,arguments=args,premises=assumptions(i))}
    lemma=theorem('component_snapshot',[['physical',plans[0]['physical_state']],['logical',L]],conditions[0],call(plans[0]['decode'],physical),logical,plans[0]['snapshot'])
    snapshot=use_with(lemma,0,[component(0),logical])
    post=lambda obs:match(obs,(['post_reply','post_committed','post_version','post_rows','post_events'],var('post_rows')),(['post_host','post_version','post_rows'],var('post_rows')))
    actions={}
    for name,source in model['actions'].items():
        rest=source['params'][1:];args=[var(n)for n,_ in rest];action=[p['actions'][name]for p in plans]
        provider=query_providers.get(name);chosen=0 if provider is None else provider;other=1-chosen
        carrier_fields=[a['result']for a in action]if provider is None else[action[chosen]['result'],plans[other]['physical_state']]
        carrier=lib.store('ProductReply_'+name,'Datatype',dict(constructors=[dict(name='Replies',fields=carrier_fields)]))
        result={'Data':carrier}
        reply_names=['left_reply','right_reply']if provider is None else['chosen_reply','preserved_state']
        execute_terms=[call(a['execute'],call(projections[i],var('initial')),*args)for i,a in enumerate(action)]if provider is None else[call(action[chosen]['execute'],call(projections[chosen],var('initial')),*args),call(projections[other],var('initial'))]
        execute=fun('execute_'+name,[['initial',P]]+rest,result,construct(carrier,0,*execute_terms))
        observe=fun('observe_'+name,[['observed',result]],source['result'],match(var('observed'),(reply_names,call(action[chosen]['observe'],var('left_reply'if provider is None else'chosen_reply')))))
        next_terms=[call(action[i]['next'],var(reply_names[i]))for i in range(2)]if provider is None else[(call(action[chosen]['next'],var('chosen_reply'))if i==chosen else var('preserved_state'))for i in range(2)]
        nextf=fun('next_'+name,[['observed',result]],P,match(var('observed'),(reply_names,construct(pair,0,*next_terms))))
        original=call(source['function'],logical,*args);executed=call(execute,physical,*args)
        obs=call(action[chosen]['observe'],call(action[chosen]['execute'],physical,*args))
        lemma=theorem('component_observation_'+name,[['physical',plans[chosen]['physical_state']],['logical',L]]+rest,conditions[chosen],obs,original,action[chosen]['observation'])
        observation={'Cases':dict(variable='physical',**{'from':call(observe,executed),'to':original},cases=[dict(bindings=['left_state','right_state'],proof=use_with(lemma,chosen,[var('left_state'if chosen==0 else'right_state'),logical,*args]))])}
        unchanged=None
        if provider is not None:
            fields=lib.objects[model['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields'];roots=['product_root_'+str(i)for i in range(len(fields))];bound=construct(model['state'],0,*map(var,roots))
            unchanged=theorem('query_state_'+name,[['logical',L]]+rest,[],post(original),logical,{'Induction':dict(variable='logical',**{'from':post(original),'to':logical},cases=[dict(bindings=roots,proof=convert(post(call(source['function'],bound,*args)),bound))])})
        preservation=[]
        for i,p in enumerate(plans):
            for j,r in enumerate(p['relations']):
                lifted=relations[offsets[i]+j]
                goal_a,goal_z=(call(lifted[side],call(nextf,executed),post(original))for side in ('left','right'))
                # Constructor cases preserve the component premises and add
                # no recursive hypothesis. Exposing the product avoids relying
                # on commuting blocked Match expressions in stored equations.
                if provider is None or i==chosen:
                    executed_i=call(action[i]['execute'],physical,*args)
                    a,z=(call(r[side],call(action[i]['next'],executed_i),post(original))for side in ('left','right'))
                    lemma=theorem(f'component_preservation_{name}_{i}_{j}',[['physical',p['physical_state']],['logical',L]]+rest,conditions[i],a,z,action[i]['preservation'][j])
                    proof=use_with(lemma,i,[var('left_state'if i==0 else'right_state'),logical,*args])
                else:
                    retained=var('left_state'if i==0 else'right_state');eq=use(unchanged,logical,*args)
                    ctx=lambda side:call(r[side],retained,var('hole'))
                    proof=trans(substitute('hole',ctx('left'),eq),hyp(offsets[i]+j),sym(substitute('hole',ctx('right'),eq)))
                preservation.append({'Cases':dict(variable='physical',**{'from':goal_a,'to':goal_z},cases=[dict(bindings=['left_state','right_state'],proof=proof)])})
        actions[name]=dict(execute=execute,result=result,observe=observe,next=nextf,observation=observation,preservation=preservation)
    plan=dict(source_objects=sorted(model['objects']),logical_state=L,physical_state=P,encode=encode,decode=decode,relations=relations,initialisation=init,snapshot=snapshot,actions=actions)
    e=entry('representation','ink-source-representation-v1',plan,refs(plan),parameters={'logical':L},result=P,effects=['source-transitions']);e['interface']['operations']=sorted(actions);rid=identity(e);lib.objects[rid]=e
    store=Store.publish(directory,lib.objects.values(),{'representations/product':rid})
    return dict(schema=1,semantics='ink-source-representation-v1',input_core_sha256=model['source'],knowledge=store.bundle([rid]),representation=rid)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('model',type=Path);p.add_argument('left',type=Path);p.add_argument('right',type=Path);p.add_argument('-o','--output',type=Path,required=True);p.add_argument('--query-provider',action='append',default=[],metavar='NAME=left|right')
    a=p.parse_args();providers={}
    for value in a.query_provider:
        name,side=value.rsplit('=',1)
        if side not in ('left','right')or name in providers:p.error('invalid or duplicate query provider')
        providers[name]=0 if side=='left'else 1
    a.output.parent.mkdir(parents=True,exist_ok=True);request=compose(json.loads(a.model.read_text()),[json.loads(a.left.read_text()),json.loads(a.right.read_text())],a.output.parent/'product-database',providers);a.output.write_text(json.dumps(request,separators=(',',':'))+'\n');print(json.dumps(dict(status='proposed',representation=request['representation'])))
if __name__=='__main__':main()
