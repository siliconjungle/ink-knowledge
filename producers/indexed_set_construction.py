"""Untrusted covering-index proofs for affine, stable Set construction.

Every proposed loop invariant, step and final observation replays in the ordinary
kernel. Source matching never grants implementation or profitability authority.
"""
import json,subprocess
from pathlib import Path
from ink_knowledge import Store,identity,semantic_entry
from producers.semantic_laws import value,var,bound,lam,op,term,arrow
from producers.contract_proofs import context_for,proof_semantics
from producers.owned_fold_contracts import instantiate
from ink_planner.semantic_search import substitute,shift

def derive(compiler,context,component,directory,framework,empty_core,builder='Build',step_name='step'):
 D=Path(directory);D.mkdir(parents=True,exist_ok=True);compiler=str(Path(compiler).resolve())
 objects=dict(component['objects']);names=dict(component['names'])
 # This finite structural family uses a map covering a private buffer's prefix.
 # The actual source record, helper and observations remain checker-bound.
 fields=dict(context['records'][builder])
 if fields!={'seen':{'Map':['U32','Bool']},'out':{'Buffer':'U32'}}:raise ValueError('unsupported indexed builder fields')
 bundle_path=D/'owned-index.json'
 r=subprocess.run([compiler,'emit-laws',str(Path(__file__).resolve().parents[1]/'libraries/owned-index-laws.ink'),'-o',str(bundle_path)],check=True,capture_output=True,text=True)
 objects.update(json.loads(bundle_path.read_text())['objects']);names.update(json.loads(r.stdout)['names'])
 b=value('Bool');u=value('U32');ls=value({'List':'U32'});m=value(fields['seen']);buf=value(fields['out']);s=value({'Named':builder})
 yes=term(b,{'Bool':True});no=term(b,{'Bool':False});nil=term(ls,'Nil')
 state=var(s,'state');item=var(u,'item');xs=var(ls,'xs')
 def trans(mid,left,right):return {'Trans':dict(middle=mid,left=left,right=right)}
 def use(i,args,types=None,assumptions=None):
  x=dict(law=i,arguments=args,premises=[])
  if types:x['types']=types
  if assumptions:x['assumptions']=assumptions
  return {'Use':x}
 def instance(i,args,types=None):
  law=objects[i]['payload']
  if types:law=instantiate(law,types)
  return substitute(law['from'],args),substitute(law['to'],args)
 def add(name,params,left,right,proof,deps=()):
  law=dict(schema=1,semantics=proof_semantics(proof),params=params,conditions=[],**{'from':left,'to':right},proof=proof,dependencies=list(deps))
  law['definition_context']=context_for(context,law)
  obj=semantic_entry(law);i=identity(obj);objects[i]=obj;names[name]=i
  bank=Store.publish(D/'bank',objects.values(),names);path=D/(name+'.json');path.write_text(json.dumps(bank.bundle([i])))
  r=subprocess.run([compiler,'knowledge-check',str(empty_core),str(path)],capture_output=True,text=True)
  (D/(name+'.receipt.json')).write_text(json.dumps(dict(status='checked'if r.returncode==0 else'rejected',stdout=r.stdout,stderr=r.stderr)))
  if r.returncode:raise ValueError(name+': '+r.stderr)
  return i
 def seen(r):return op(m,'field:seen',r)
 def out(r):return op(buf,'field:out',r)
 def logical(r):return op(ls,'method:freeze',out(r))
 def distinct(x):return op(b,'call:'+component['valid_name'],x)
 def member(x,y):return op(b,'call:'+component['member_name'],x,y)
 def covered(x,index):
  callback=lam(u,lam(b,op(b,'binary:&&',op(b,'method:contains',shift(index,2),bound(u,1)),bound(b,0))))
  return op(b,'call:foldr',x,yes,callback)
 def valid(r):return op(b,'binary:&&',distinct(logical(r)),covered(logical(r),seen(r)))
 def step(x,r):return op(s,'call:'+step_name,x,r)
 def one(x):return term(ls,{'Cons':[x,nil]})
 def concat(x,y):return op(ls,'method:concat',x,y)
 def assert_true(p,proof,body):
  proposition=op(b,'binary:==',p,yes);mid=op(b,'binary:==',yes,yes)
  return {'AssertEquality':dict(equality={'from':p,'to':yes},premise=trans(mid,{'Congruence':[proof,'Normalize']},'Normalize'),body=body)}
 old=logical(state);index=seen(state);updated=op(m,'method:set',index,item,yes);appended=concat(old,one(item))
 args=dict(xs=old,seen=index,item=item)
 cover_i=names['coverage_insert_u32'];cover_from,_=instance(cover_i,args)
 cover_proof=trans(cover_from,'Normalize',use(cover_i,args))
 kept=trans(covered(old,updated),'Normalize',cover_proof)
 append_i=names['coverage_append_u32']
 growing=trans(covered(appended,updated),'Normalize',trans(covered(old,updated),use(append_i,args),cover_proof))
 absent_i=names['absent_from_covered_u32'];absent_from,_=instance(absent_i,args)
 absence=trans(absent_from,'Normalize',use(absent_i,args))
 absent_property=op(b,'binary:==',member(old,item),no)
 append_law=names['scan_append'];append_args=dict(xs=old,item=item)
 append_from,append_to=instance(append_law,append_args)
 distinct_append=trans(append_to,use(append_law,append_args),'Normalize')
 new_case=assert_true(distinct(appended),distinct_append,growing)
 new_case=assert_true(absent_property,absence,new_case)
 cases={'Cases':dict(condition=op(b,'method:contains',index,item),on_true=kept,on_false=new_case)}
 cases={'Cases':dict(condition=covered(old,index),on_true=cases,on_false='Normalize')}
 cases={'Cases':dict(condition=distinct(old),on_true=cases,on_false='Normalize')}
 guarded=op(b,'call:choose',valid(state),valid(step(item,state)),yes)
 step_id=add('indexed_step_preserves',dict(state=s,item=u),guarded,yes,cases,[cover_i,append_i,absent_i,append_law])
 initial=op(s,'record:'+builder,op(m,'local:map-empty'),op(buf,'local:buffer-empty'))
 callback=lam(u,lam(s,step(bound(u,1),bound(s,0))))
 predicate=lam(s,valid(bound(s,0)));accept=lam(u,yes)
 folded=op(s,'call:foldl',xs,initial,callback)
 fold_i=names['foldl_preserves'];args=dict(xs=xs,initial=initial,step=callback,valid=predicate,accept=accept)
 fold_from,_=instance(fold_i,args,{'A':'U32','S':s['Value']})
 assumed_state=var(s,'__assumed_state');assumed_item=var(u,'__assumed_item')
 step_args=dict(state=assumed_state,item=assumed_item);step_from,_=instance(step_id,step_args)
 assumption=trans(step_from,'Normalize',use(step_id,step_args))
 all_i=names['all_true'];all_args=dict(xs=xs);all_from,_=instance(all_i,all_args,{'A':'U32'})
 all_proof=trans(all_from,'Normalize',use(all_i,all_args,{'A':'U32'}))
 middle=op(b,'call:choose',op(b,'binary:&&',op(b,'apply',predicate,initial),yes),valid(folded),yes)
 guard={'Congruence':[{'Congruence':['Normalize',all_proof]},'Normalize','Normalize']}
 bridge=trans(middle,guard,'Normalize')
 fold_proof=trans(fold_from,{'Sym':bridge},use(fold_i,args,{'A':'U32','S':s['Value']},[assumption]))
 fold_id=add('indexed_construct_valid',dict(xs=ls),valid(folded),yes,fold_proof,[step_id,fold_i,all_i])
 observed=distinct(logical(folded))
 proof={'Cases':dict(condition=observed,on_true='Normalize',on_false=trans(valid(folded),'Normalize',use(fold_id,dict(xs=xs))))}
 construction=add('indexed_construct_distinct',dict(xs=ls),observed,yes,proof,[fold_id])
 return dict(objects=objects,names=names,construction=construction)
