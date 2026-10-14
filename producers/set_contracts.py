"""Untrusted preservation proofs for a prefix-based set interface.

Source structure chooses candidate helpers; no name, hash or observation grants
validity. Each ordinary semantic lemma and the final source obligation must replay.
Algorithms remain source definitions and shared fold laws stay canonical objects.
"""
import json,subprocess
from pathlib import Path
from ink_knowledge import Store,identity,semantic_entry
from producers.semantic_laws import value,var,bound,lam,op,term,arrow
from producers.contract_proofs import context_for,proof_semantics
from producers.beta_specialization15 import beta_normalize
from producers.owned_fold_contracts import instantiate
from ink_planner.semantic_search import substitute

def derive(compiler,definition_context,directory,framework_directory,empty_core,scan_name=None):
 D=Path(directory);D.mkdir(parents=True,exist_ok=True)
 compiler=str(Path(compiler).resolve())
 context=definition_context;defs={n:r['definition'] for n,r in context['definitions'].items()}
 objects={};names={}
 for stem in ['storage','local','general','filter']:
  bundle=json.loads((framework_directory/(stem+'-laws.json')).read_text());objects.update(bundle['objects'])
  receipt=json.loads((framework_directory/(stem+'-laws.log')).read_text().splitlines()[-1]);names.update(receipt['names'])
 bool_sort=value('Bool');yes=term(bool_sort,{'Bool':True});no=term(bool_sort,{'Bool':False})
 def operation(t,name):return isinstance(t.get('node'),dict) and t['node'].get('Op',[None])[0]==name
 scan=scan_name or next(n for n,d in defs.items()if operation(beta_normalize(d['body']),'call:foldl') and isinstance(d['result'],dict)and 'Named'in d['result'])
 scan_body=beta_normalize(defs[scan]['body']);scan_args=scan_body['node']['Op'][1];initial,step=scan_args[1:];s=initial['sort'];ls=scan_args[0]['sort'];t=ls['Value']['List'];a=value(t)
 distinct=next(n for n,d in defs.items()if d['result']=='Bool' and len(d['params'])==1 and d['params'][0][1]==ls['Value'] and operation(beta_normalize(d['body']),'field:valid') and beta_normalize(d['body'])['node']['Op'][1][0]['node'].get('Op',[None])[0]=='call:'+scan)
 member=next(n for n,d in defs.items()if [ty for _,ty in d['params']]==[ls['Value'],t] and d['result']=='Bool' and operation(beta_normalize(d['body']),'call:foldr'))
 append_new=next(n for n,d in defs.items()if [ty for _,ty in d['params']]==[ls['Value'],t] and d['result']==ls['Value'] and operation(beta_normalize(d['body']),'call:choose'))
 xs=var(ls,'xs');item=var(a,'item');nil=term(ls,'Nil');one=term(ls,{'Cons':[item,nil]});concat=lambda x,y:op(ls,'method:concat',x,y)
 sc=lambda x:op(s,'call:'+scan,x);seen=lambda x:op(ls,'field:seen',x);valid=lambda x:op(bool_sort,'call:'+distinct,x);mem=lambda x,y:op(bool_sort,'call:'+member,x,y)
 def trans(middle,left,right):return {'Trans':dict(middle=middle,left=left,right=right)}
 def use(ident,args,types=None,premises=None,assumptions=None):
  result=dict(law=ident,arguments=args,premises=premises or [])
  if types:result['types']=types
  if assumptions:result['assumptions']=assumptions
  return {'Use':result}
 def instance(ident,args,types=None):
  law=objects[ident]['payload']
  if types:law=instantiate(law,types)
  return substitute(law['from'],args),substitute(law['to'],args)
 def add(name,params,left,right,proof,deps=(),conditions=()):
  law=dict(schema=1,semantics=proof_semantics(proof),params=params,conditions=list(conditions),**{'from':left,'to':right},proof=proof,dependencies=list(deps))
  law['definition_context']=context_for(context,law)
  obj=semantic_entry(law);ident=identity(obj);objects[ident]=obj;names[name]=ident
  bank=Store.publish(D/'bank',objects.values(),names)
  path=D/(name+'.json');path.write_text(json.dumps(bank.bundle([ident])))
  result=subprocess.run([compiler,'knowledge-check',str(empty_core),str(path)],capture_output=True,text=True)
  (D/(name+'.receipt.json')).write_text(json.dumps(dict(status='checked' if result.returncode==0 else 'rejected',stdout=result.stdout,stderr=result.stderr)))
  if result.returncode:raise ValueError(name+': '+result.stderr.strip())
  return ident
 # The prefix observer is justified by the general per-step observer assumption.
 observer=lam(s,seen(bound(s,0)))
 args=dict(xs=xs,initial=initial,step=step,observe=observer)
 ident=names['foldl_observe_append'];left,right=instance(ident,args,{'A':t,'S':s['Value']})
 proof=trans(left,'Normalize',trans(right,use(ident,args,{'A':t,'S':s['Value']},assumptions=['Normalize']),'Normalize'))
 observed=add('scan_prefix',{'xs':ls},seen(sc(xs)),xs,proof,[ident])
 # Appending one element continues the exact left-fold scan.
 f=lam(s,lam(a,op(s,'apply',op(step['sort']['Arrow'][1],'apply',step,bound(a,0)),bound(s,1))))
 ident=names['foldl_append'];args=dict(xs=xs,ys=one,s=initial,f=f);left,right=instance(ident,args,{'A':t,'S':s['Value']})
 left_valid=op(bool_sort,'field:valid',left);right_valid=op(bool_sort,'field:valid',right)
 start=valid(concat(xs,one));before=op(bool_sort,'binary:&&',valid(xs),op(bool_sort,'binary:==',mem(seen(sc(xs)),item),no));finish=op(bool_sort,'binary:&&',valid(xs),op(bool_sort,'binary:==',mem(xs,item),no))
 prefix_use=use(observed,dict(xs=xs))
 rewrite={'Congruence':['Normalize',{'Congruence':[{'Congruence':[prefix_use,'Normalize']},'Normalize']}]}
 proof=trans(left_valid,'Normalize',trans(right_valid,{'Congruence':[use(ident,args,{'A':t,'S':s['Value']})]},trans(before,'Normalize',rewrite)))
 append=add('scan_append',{'xs':ls,'item':a},start,finish,proof,[ident,observed])
 
 # Inserting a previously absent item preserves the predicate.
 insert=lambda x,y:op(ls,'call:'+append_new,x,y)
 condition=dict(**{'from':valid(xs),'to':yes})
 case=mem(xs,item)
 false=trans(start,'Normalize',trans(finish,use(append,dict(xs=xs,item=item)),'Normalize'))
 proof={'Cases':dict(condition=case,on_true='Normalize',on_false=false)}
 insert_valid=add('insert_preserves',{'xs':ls,'item':a},valid(insert(xs,item)),yes,proof,[append],[condition])
 # The general fold law composes the one-step preservation into construction.
 initial_list=var(ls,'initial')
 insert_step=lam(a,lam(ls,insert(bound(ls,0),bound(a,1))))
 valid_fn=lam(ls,valid(bound(ls,0)))
 accept=lam(a,yes)
 ident=names['foldl_preserves'];args=dict(xs=xs,initial=initial_list,step=insert_step,valid=valid_fn,accept=accept)
 left,right=instance(ident,args,{'A':t,'S':ls['Value']})
 folded=op(ls,'call:foldl',xs,initial_list,insert_step);want=op(bool_sort,'call:choose',valid(initial_list),valid(folded),yes)
 assumed_state=var(ls,'__assumed_state');assumed_item=var(a,'__assumed_item')
 assumption=trans(valid(insert(assumed_state,assumed_item)),'Normalize',use(insert_valid,dict(xs=assumed_state,item=assumed_item),premises=[trans(op(bool_sort,'apply',valid_fn,assumed_state),'Normalize',{'Hypothesis':1})]))
 all_args=dict(xs=xs);all_left,all_right=instance(names['all_true'],all_args,{'A':t})
 actual_guard=left['node']['Op'][1][0]['node']['Op'][1][1]
 guard_proof=trans(all_left,'Normalize',use(names['all_true'],dict(xs=xs),{'A':t}))
 # Reduce the guard in the left side by the independently checked all-true law.
 guard_rewrite={'Congruence':[{'Congruence':['Normalize',guard_proof]},'Normalize','Normalize']}
 chosen=op(bool_sort,'call:choose',op(bool_sort,'binary:&&',op(bool_sort,'apply',valid_fn,initial_list),yes),valid(folded),yes)
 bridge=trans(chosen,guard_rewrite,'Normalize')
 proof=trans(left,{'Sym':bridge},use(ident,args,{'A':t,'S':ls['Value']},assumptions=[assumption]))
 fold_preserves=add('fold_preserves',{'xs':ls,'initial':ls},want,yes,proof,[ident,insert_valid,names['all_true']])
 construct_args=dict(xs=xs,initial=nil)
 construct_goal=valid(op(ls,'call:foldl',xs,nil,insert_step))
 cfrom,cto=instance(fold_preserves,construct_args)
 construct=add('construct_preserves',{'xs':ls},construct_goal,yes,trans(cfrom,'Normalize',use(fold_preserves,construct_args)),[fold_preserves])
 
 # Filtering cannot create a member that was absent from the original list.
 pred_sort=arrow(a,bool_sort);predicate=var(pred_sort,'p')
 filtered=lambda x:op(ls,'method:filter',x,predicate)
 absent=lambda x:op(bool_sort,'binary:==',mem(x,item),no)
 absence=op(bool_sort,'call:choose',absent(xs),absent(filtered(xs)),yes)
 head=var(a,'head');tail=var(ls,'tail')
 branches='Normalize'
 for condition in [mem(tail,item),op(bool_sort,'binary:==',term(ls,{'Cons':[head,nil]}),one),op(bool_sort,'apply',predicate,head)]:
  branches={'Cases':dict(condition=condition,on_true=branches,on_false=branches)}
 proof={'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step=branches)}
 filter_absent=add('filter_absent',{'xs':ls,'item':a,'p':pred_sort},absence,yes,proof)
 # Two scans maintain the prefix/subsequence relation under the same ordered input.
 raw_valid=lambda state:op(bool_sort,'field:valid',state)
 beq=lambda x,y:op(bool_sort,'binary:==',x,y)
 relation=lambda full,kept:op(bool_sort,'binary:&&',beq(seen(kept),filtered(seen(full))),op(bool_sort,'call:choose',raw_valid(full),raw_valid(kept),yes))
 scan_step_name=step['node']['Lambda']['node']['Lambda']['node']['Op'][0]
 advance=lambda x,state:op(s,scan_step_name,x,state)
 keep_advance=lambda x,state:op(s,'call:choose',op(bool_sort,'apply',predicate,x),advance(x,state),state)
 full=var(s,'full');kept=var(s,'kept')
 new_relation=relation(advance(item,full),keep_advance(item,kept))
 def assert_true(proposition,proposition_proof,body):
  premise=trans(beq(yes,yes),{'Congruence':[proposition_proof,'Normalize']},'Normalize')
  return {'AssertEquality':dict(equality=dict(**{'from':proposition,'to':yes}),premise=premise,body=body)}
 filter_args=dict(xs=seen(full),ys=one,p=predicate);cat_from,cat_to=instance(names['filter_append'],filter_args,{'A':t})
 cat_equality=beq(cat_from,cat_to)
 cat_proof=trans(beq(cat_to,cat_to),{'Congruence':[use(names['filter_append'],filter_args,{'A':t}),'Normalize']},'Normalize')
 absence_args=dict(xs=seen(full),item=item,p=predicate);afrom,ato=instance(filter_absent,absence_args)
 absent_property=beq(mem(filtered(seen(full)),item),no)
 absent_proof=trans(afrom,'Normalize',use(filter_absent,absence_args))
 member_branch={'Cases':dict(condition=mem(seen(full),item),on_true='Normalize',on_false=assert_true(absent_property,absent_proof,'Normalize'))}
 old_relation=relation(full,kept)
 prefix_prop=beq(seen(kept),filtered(seen(full)))
 prefix_proof={'Cases':dict(condition=prefix_prop,on_true='Normalize',on_false=trans(old_relation,'Normalize',{'Hypothesis':0}))}
 kept_proof={'Cases':dict(condition=raw_valid(kept),on_true='Normalize',on_false=trans(old_relation,'Normalize',{'Hypothesis':0}))}
 kept_proof={'Cases':dict(condition=prefix_prop,on_true=kept_proof,on_false=kept_proof)}
 when_valid={'Cases':dict(condition=op(bool_sort,'apply',predicate,item),on_true=member_branch,on_false=member_branch)}
 when_valid=assert_true(raw_valid(kept),kept_proof,when_valid)
 when_invalid={'Cases':dict(condition=op(bool_sort,'apply',predicate,item),on_true='Normalize',on_false='Normalize')}
 branch={'Cases':dict(condition=raw_valid(full),on_true=when_valid,on_false=when_invalid)}
 branch=assert_true(prefix_prop,prefix_proof,branch)
 empty_args=dict(xs=filtered(seen(full)))
 empty_from,empty_to=instance(names['concat_empty'],empty_args,{'A':t})
 empty_proof=trans(beq(empty_to,empty_to),{'Congruence':[use(names['concat_empty'],empty_args,{'A':t}),'Normalize']},'Normalize')
 proof=assert_true(cat_equality,cat_proof,assert_true(beq(empty_from,empty_to),empty_proof,branch))
 step_relation=add('scan_filter_step',{'full':s,'kept':s,'item':a,'p':pred_sort},new_relation,yes,proof,[names['filter_append'],names['concat_empty'],filter_absent],[dict(**{'from':relation(full,kept),'to':yes})])
 # Compose the step relation, then bind the filtered fold to the same source scan.
 relate_fn=lam(s,lam(s,relation(bound(s,1),bound(s,0))))
 logical_step=lam(a,lam(s,keep_advance(bound(a,1),bound(s,0))))
 sim_args=dict(xs=xs,physical=initial,logical=initial,physical_step=step,logical_step=logical_step,relate=relate_fn)
 sim_from,sim_to=instance(names['foldl_simulates'],sim_args,{'A':t,'P':s['Value'],'L':s['Value']})
 assumed_full=var(s,'__assumed_p');assumed_kept=var(s,'__assumed_l')
 old_condition=op(bool_sort,'apply',op(relate_fn['sort']['Arrow'][1],'apply',relate_fn,assumed_full),assumed_kept)
 step_args=dict(full=assumed_full,kept=assumed_kept,item=assumed_item,p=predicate)
 step_from,step_to=instance(step_relation,step_args)
 step_assumption=trans(step_from,'Normalize',use(step_relation,step_args,premises=[trans(old_condition,'Normalize',{'Hypothesis':0})]))
 ff_args=dict(xs=xs,initial=initial,p=predicate,step=step)
 ff_from,ff_to=instance(names['foldl_filter'],ff_args,{'A':t,'S':s['Value']})
 def observed_filter_bridge(field):
  start=op(ls if field=='seen'else bool_sort,'field:'+field,sc(filtered(xs)))
  middle=op(start['sort'],'field:'+field,ff_from)
  return trans(middle,'Normalize',{'Congruence':[use(names['foldl_filter'],ff_args,{'A':t,'S':s['Value']})]})
 relation_bridge={'Congruence':[{'Congruence':[observed_filter_bridge('seen'),'Normalize']},{'Congruence':['Normalize',observed_filter_bridge('valid'),'Normalize']}]}
 related_mid=relation(sc(xs),ff_to)
 proof=trans(sim_from,trans(related_mid,relation_bridge,'Normalize'),use(names['foldl_simulates'],sim_args,{'A':t,'P':s['Value'],'L':s['Value']},assumptions=[step_assumption]))
 scan_filter=add('scan_filter_relation',{'xs':ls,'p':pred_sort},relation(sc(xs),sc(filtered(xs))),yes,proof,[names['foldl_simulates'],names['foldl_filter'],step_relation])
 filter_guard=op(bool_sort,'call:choose',valid(xs),valid(filtered(xs)),yes)
 related_use=use(scan_filter,dict(xs=xs,p=predicate));related_from,related_to=instance(scan_filter,dict(xs=xs,p=predicate))
 prefix_condition=beq(seen(sc(filtered(xs))),filtered(seen(sc(xs))))
 proof={'Cases':dict(condition=prefix_condition,on_true=trans(related_from,'Normalize',related_use),on_false={'Cases':dict(condition=filter_guard,on_true='Normalize',on_false=trans(related_from,'Normalize',related_use))})}
 filter_preserves=add('filter_preserves',{'xs':ls,'p':pred_sort},filter_guard,yes,proof,[scan_filter])
 
 return dict(objects=objects,names=names,construct=construct,fold=fold_preserves,filter=filter_preserves,element_type=t,insert_step=insert_step,valid_name=distinct,member_name=member)

from producers.contract_proofs import ProofSession,pure_proposals
from producers.owned_fold_contracts import closed
from ink_planner.semantic_search import positions,map_children


def author(compiler,source,directory,framework_directory=None,*,max_attempts=4096,max_unfold_work=100_000):
 if not 1<=max_attempts<=65_536 or not 1<=max_unfold_work<=1_000_000:raise ValueError("set authoring resource budget")
 D=Path(directory).resolve();D.mkdir(parents=True,exist_ok=True)
 compiler=str(Path(compiler).resolve());source=str(Path(source).resolve())
 framework_directory=Path(framework_directory).resolve()if framework_directory else D/'framework'
 framework_directory.mkdir(parents=True,exist_ok=True)
 libraries=Path(__file__).resolve().parents[1]/'libraries'
 for stem,name in [('storage','storage-observations.ink'),('local','local-relations.ink'),('general','general-laws.ink'),('filter','sequence-filter-laws.ink')]:
  command=[compiler,'emit-laws',str(libraries/name),'-o',str(framework_directory/(stem+'-laws.json'))]
  result=subprocess.run(command,check=True,capture_output=True,text=True)
  (framework_directory/(stem+'-laws.log')).write_text(result.stdout)
 (D/'empty.ink').write_text('module unrelated;fn identity(x:u32)->u32{return x;}\n')
 subprocess.run([compiler,'emit-core',str(D/'empty.ink'),'-o',str(D/'empty.core.json')],check=True,capture_output=True,text=True)
 subprocess.run([compiler,'emit-contract-obligations',source,'-o',str(D/'scan-obligations.json')],check=True)
 goals=json.loads((D/'scan-obligations.json').read_text());context=goals['definition_context']
 unfold_work=[0]
 def unfold(t,depth=0):
  unfold_work[0]+=1
  if unfold_work[0]>max_unfold_work:raise ValueError("source helper unfolding work budget")
  if depth>64:raise ValueError('source helper unfolding depth')
  t=map_children(t,lambda c:unfold(c,depth+1));node=t['node']
  operation=node.get('Op')if isinstance(node,dict)else None
  if operation and operation[0].startswith('call:') and operation[0][5:] in context['definitions']:
   definition=context['definitions'][operation[0][5:]]['definition']
   body=substitute(definition['body'],dict(zip([n for n,_ in definition['params']],operation[1])))
   return unfold(body,depth+1)
  return t
 scans=[]
 for n,r in context['definitions'].items():
  d=r['definition'];result=d['result']
  if not isinstance(result,dict) or 'Named'not in result:continue
  fields=dict(context['records'].get(result['Named'],[]))
  if set(fields)!={'seen','valid'} or fields['valid']!='Bool' or not isinstance(fields['seen'],dict) or 'List'not in fields['seen']:continue
  if beta_normalize(d['body'])['node'].get('Op',[None])[0]=='call:foldl':scans.append(n)
 components=[derive(compiler,context,D/('components-'+n),framework_directory,D/'empty.core.json',n)for n in scans]
 objects={}; roots=[];proofs={};names={}
 for component in components:objects.update(component['objects'])
 with ProofSession(compiler,source,[],goals['source_sha256'])as session:
  for goal in goals['pure']:
   proof=next((p for p in pure_proposals(goal)if session.check(goal['name'],p,None)['status']=='checked'),None)
   deps=[]
   if proof is None:
    attempts=0;unfold_work[0]=0
    proposal_bank=Store.publish(D/'proposal-bank',objects.values());bundle_cache={}
    for component in components:
     candidates=[component['construct'],component['fold'],component['filter']]
     for ident in candidates:
      law=objects[ident]['payload'];params=law['params']
      # Propose list/fold/filter arguments from the real typed obligation. Only
      # matching scalar families are attempted; final replay checks every binder.
      terms={}
      unfold_work[0]=0
      for n,sort in goal['params'].items():terms[json.dumps(var(sort,n),sort_keys=True)]=var(sort,n)
      for term in [goal['goal']['from'],*sum(([c['from'],c['to']]for c in goal['conditions']),[])]:
       for _,t in positions(beta_normalize(unfold(term))):
        if closed(t):terms[json.dumps(t,sort_keys=True)]=t
      import itertools
      choices=[[t for t in terms.values()if t['sort']==sort]for sort in params.values()]
      for values in itertools.product(*choices):
       attempts+=1
       if attempts>max_attempts:raise ValueError('set proof proposal budget for '+goal['name'])
       args=dict(zip(params,values));middle=substitute(law['from'],args)
       trial={'Trans':dict(middle=middle,left='Normalize',right={'Use':dict(law=ident,arguments=args,premises=[])})}
       if ident not in bundle_cache:bundle_cache[ident]=proposal_bank.bundle([ident])
       bundle=bundle_cache[ident]
       if session.check(goal['name'],trial,bundle)['status']=='checked':proof=trial;deps=[ident];break
      if proof is not None:break
     if proof is not None:break
   if proof is None:raise ValueError('no checked proof for '+goal['name'])
   law=dict(schema=1,semantics=proof_semantics(proof),params=goal['params'],conditions=goal['conditions'],**goal['goal'],proof=proof,dependencies=deps)
   law['definition_context']=context_for(context,goal)
   obj=semantic_entry(law);ident=identity(obj);objects[ident]=obj;roots.append(ident);names['contract.'+goal['name']]=ident
   proofs[goal['name']]={'Use':dict(law=ident,arguments={n:var(sort,n)for n,sort in goal['params'].items()},premises=[{'Hypothesis':i}for i in range(len(goal['conditions']))])}
 bank=Store.publish(D/'proofs',objects.values(),names)
 evidence=dict(schema=1,semantics=goals['semantics'],source_sha256=goals['source_sha256'],proofs=proofs,state_proofs={},knowledge=bank.bundle(roots),state_knowledge=None)
 (D/'evidence.json').write_text(json.dumps(evidence,separators=(',',':'))+'\n')
 if goals.get('state') is not None:
  from producers.contract_proofs import author as author_contracts
  evidence,bank=author_contracts(compiler,source,D/'complete',source_evidence=str(D/'evidence.json'))
  (D/'evidence.json').write_text(json.dumps(evidence,separators=(',',':'))+'\n')
 subprocess.run([compiler,'check-contracts',source,'--contract-proofs',str(D/'evidence.json')],check=True)
 return evidence,bank

if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('source');parser.add_argument('output');parser.add_argument('--compiler',required=True)
 args=parser.parse_args();evidence,bank=author(args.compiler,args.source,args.output)
 print(json.dumps(dict(status='checked',pure=len(evidence['proofs']),objects=len(evidence['knowledge']['objects']),snapshot=bank.snapshot_id)))
