"""Untrusted complete-value simulation proposals for indexed construction.

The source helper and every list induction/loop observation are replayed by the
ordinary kernel. This module supplies no algorithm admission authority.
"""
import json,subprocess
from pathlib import Path
from ink_knowledge import Store,identity,semantic_entry
from producers.semantic_laws import value,var,bound,lam,op,term
from producers.contract_proofs import context_for,proof_semantics
from producers.owned_fold_contracts import instantiate
from ink_planner.semantic_search import substitute,shift

def derive(compiler,context,component,directory,empty_core,builder='Build',step_name='step'):
 D=Path(directory);D.mkdir(parents=True,exist_ok=True)
 objects=dict(component['objects']);names=dict(component['names'])
 b=value('Bool');u=value('U32');ls=value({'List':'U32'});m=value({'Map':['U32','Bool']});buf=value({'Buffer':'U32'});s=value({'Named':builder})
 if dict(context['records'][builder])!={'seen':m['Value'],'out':buf['Value']}:raise ValueError('indexed simulation builder fields')
 yes=term(b,{'Bool':True});no=term(b,{'Bool':False});nil=term(ls,'Nil')
 xs=var(ls,'xs');item=var(u,'item');head=var(u,'head');tail=var(ls,'tail')
 def trans(mid,left,right):return {'Trans':dict(middle=mid,left=left,right=right)}
 def use(i,args,types=None,assumptions=None):
  result=dict(law=i,arguments=args,premises=[])
  if types:result['types']=types
  if assumptions:result['assumptions']=assumptions
  return {'Use':result}
 def instance(i,args,types=None):
  law=objects[i]['payload']
  if types:law=instantiate(law,types)
  return substitute(law['from'],args),substitute(law['to'],args)
 def add(name,params,left,right,proof,deps=()):
  law=dict(schema=1,semantics=proof_semantics(proof),params=params,conditions=[],**{'from':left,'to':right},proof=proof,dependencies=list(deps))
  law['definition_context']=context_for(context,law)
  obj=semantic_entry(law);ident=identity(obj);objects[ident]=obj;names[name]=ident
  bank=Store.publish(D/'bank',objects.values(),names);path=D/(name+'.json');path.write_text(json.dumps(bank.bundle([ident])))
  result=subprocess.run([str(compiler),'knowledge-check',str(empty_core),str(path)],capture_output=True,text=True)
  (D/(name+'.receipt.json')).write_text(json.dumps(dict(status='checked'if result.returncode==0 else'rejected',stdout=result.stdout,stderr=result.stderr)))
  if result.returncode:raise ValueError(name+': '+result.stderr)
  return ident
 def eq(x,y):return op(b,'binary:==',x,y)
 def choose(c,x,y):return op(x['sort'],'call:choose',c,x,y)
 def one(x):return term(ls,{'Cons':[x,nil]})
 def cons(x,rest):return term(ls,{'Cons':[x,rest]})
 def concat(x,y):return op(ls,'method:concat',x,y)
 def forward(rows,key):
  # Application binds the captured key before the two fold binders.
  callback=lam(u,lam(u,lam(b,op(b,'binary:||',eq(bound(u,2),bound(u,1)),bound(b,0)))))
  return op(b,'call:foldr',rows,no,op(callback['sort']['Arrow'][1],'apply',callback,key))
 def inserted(rows,key):return op(ls,'local:keys-insert',rows,key)
 target=lambda rows,key:choose(forward(rows,key),rows,concat(rows,one(key)))
 libraries=Path(__file__).resolve().parents[1]/'libraries'
 for stem in ['indexed-sequence','sequence-coverage','owned-index']:
  result=subprocess.run([str(compiler),'emit-laws',str(libraries/(stem+'-laws.ink')),'-o',str(D/(stem+'.json'))],check=True,capture_output=True,text=True)
  objects.update(json.loads((D/(stem+'.json')).read_text())['objects']);names.update(json.loads(result.stdout)['names'])
 pred_sort=lam(u,yes)['sort'];p=var(pred_sort,'p')
 def apply(predicate,key):return op(b,'apply',predicate,key)
 def all_rows(rows,predicate):
  callback=lam(u,lam(b,op(b,'binary:&&',apply(shift(predicate,2),bound(u,1)),bound(b,0))))
  return op(b,'call:foldr',rows,yes,callback)
 def covered(rows,index):return all_rows(rows,lam(u,op(b,'method:contains',shift(index,1),bound(u,0))))
 def membership(rows):return lam(u,forward(shift(rows,1),bound(u,0)))
 guard=op(b,'binary:&&',all_rows(xs,p),apply(p,item))
 insert_goal=choose(guard,all_rows(inserted(xs,item),p),yes)
 tail_guard=op(b,'binary:&&',all_rows(tail,p),apply(p,item))
 tail_goal=choose(tail_guard,all_rows(inserted(tail,item),p),yes)
 recurse=trans(tail_goal,'Normalize',{'Hypothesis':0})
 cases={'Cases':dict(condition=op(b,'binary:<',item,head),on_true='Normalize',on_false=recurse)}
 cases={'Cases':dict(condition=eq(item,head),on_true='Normalize',on_false=cases)}
 for condition in [apply(p,item),all_rows(tail,p),apply(p,head)]:
  cases={'Cases':dict(condition=condition,on_true=cases,on_false='Normalize')}
 proof={'Induction':dict(variable='xs',names=['head','tail'],base={'Cases':dict(condition=apply(p,item),on_true='Normalize',on_false='Normalize')},step=cases)}
 insert_id=add('key_insertion_preserves_coverage_u32',dict(xs=ls,item=u,p=pred_sort),insert_goal,yes,proof)
 direction_id=names['membership_direction_u32']
 physical=var(s,'physical');logical=var(ls,'logical')
 def seen(state):return op(m,'field:seen',state)
 def keys(state):return op(ls,'method:keys',seen(state))
 def output(state):return op(ls,'method:freeze',op(buf,'field:out',state))
 def relation(state,rows):return op(b,'binary:&&',eq(output(state),rows),op(b,'binary:&&',covered(rows,seen(state)),all_rows(keys(state),membership(rows))))
 def logical_step(key,rows):
  callback=component['insert_step']
  return op(ls,'apply',op(callback['sort']['Arrow'][1],'apply',callback,key),rows)
 def physical_step(key,state):return op(s,'call:'+step_name,key,state)
 def assert_eq(left,right,premise,body):return {'AssertEquality':dict(equality={'from':left,'to':right},premise=premise,body=body)}
 def assert_true(proposition,proof,body):
  premise=trans(eq(yes,yes),{'Congruence':[proof,'Normalize']},'Normalize')
  return assert_eq(proposition,yes,premise,body)
 def implied(predicate):
  return {'Cases':dict(condition=predicate,on_true='Normalize',on_false=trans(relation(physical,logical),'Normalize',{'Hypothesis':0}))}
 old=relation(physical,logical);member=op(b,'call:'+component['member_name'],logical,item)
 direction_from,direction_to=instance(direction_id,dict(xs=logical,item=item))
 direction_bool=trans(eq(direction_to,direction_to),{'Congruence':[use(direction_id,dict(xs=logical,item=item)),'Normalize']},'Normalize')
 index=seen(physical);old_keys=keys(physical);new_index=op(m,'method:set',index,item,yes)
 contains=op(b,'method:contains',index,item)
 reverse=all_rows(old_keys,membership(logical));coverage=covered(logical,index)
 witness_id=names['covered_witness_u32'];witness_args=dict(xs=old_keys,item=item,p=membership(logical));witness_from,_=instance(witness_id,witness_args)
 absence_id=names['absent_from_covered_u32'];absence_args=dict(xs=logical,seen=index,item=item);absence_from,_=instance(absence_id,absence_args)
 present_cases={'Cases':dict(condition=member,on_true='Normalize',on_false=trans(witness_from,'Normalize',use(witness_id,witness_args)))}
 absent_cases={'Cases':dict(condition=member,on_true=trans(absence_from,'Normalize',use(absence_id,absence_args)),on_false='Normalize')}
 condition_proof={'Cases':dict(condition=contains,on_true=present_cases,on_false=absent_cases)}
 condition_bool=eq(contains,member)
 def finish(present):
  next_rows=logical if present else concat(logical,one(item))
  predicate=membership(next_rows)
  next_reverse=all_rows(inserted(old_keys,item),predicate)
  insert_args=dict(xs=old_keys,item=item,p=predicate);insert_from,_=instance(insert_id,insert_args)
  reverse_proof=trans(insert_from,'Normalize',use(insert_id,insert_args))
  body=assert_true(next_reverse,reverse_proof,'Normalize')
  if not present:
   monotone_id=names['all_monotone'];monotone_args=dict(xs=old_keys,p=membership(logical),q=predicate)
   mono_from,_=instance(monotone_id,monotone_args,{'A':'U32'})
   query=var(u,'__assumed_item');append_id=names['member_append_u32'];append_args=dict(xs=logical,added=item,key=query)
   append_from,append_to=instance(append_id,append_args)
   append_assumption=trans(append_from,'Normalize',trans(append_to,use(append_id,append_args),'Normalize'))
   append_assumption={'Cases':dict(condition=eq(query,item),on_true=append_assumption,on_false=append_assumption)}
   monotone_proof=trans(mono_from,'Normalize',use(monotone_id,monotone_args,{'A':'U32'},[append_assumption]))
   self_args=dict(xs=logical,added=item,key=item);self_from,self_to=instance(append_id,self_args)
   self_proof=trans(self_from,'Normalize',trans(self_to,use(append_id,self_args),'Normalize'))
   body=assert_true(apply(predicate,item),self_proof,body)
   body=assert_true(all_rows(old_keys,predicate),monotone_proof,body)
  cover_id=names['coverage_insert_u32'];cover_args=dict(xs=logical,seen=index,item=item);cover_from,_=instance(cover_id,cover_args)
  cover_proof=trans(cover_from,'Normalize',use(cover_id,cover_args))
  if not present:
   append_cover=names['coverage_append_u32'];append_args=dict(xs=logical,seen=index,item=item)
   append_from,append_to=instance(append_cover,append_args)
   cover_proof=trans(append_from,'Normalize',trans(append_to,use(append_cover,append_args),trans(covered(logical,new_index),'Normalize',cover_proof)))
  return assert_true(covered(next_rows,new_index),cover_proof,body)
 branches={'Cases':dict(condition=member,on_true=finish(True),on_false=finish(False))}
 branches=assert_eq(contains,member,condition_proof,branches)
 branches=assert_eq(direction_from,direction_to,direction_bool,branches)
 branches=assert_true(reverse,implied(reverse),branches)
 branches=assert_true(coverage,implied(coverage),branches)
 branches=assert_true(eq(output(physical),logical),implied(eq(output(physical),logical)),branches)
 step_proof={'Cases':dict(condition=old,on_true=branches,on_false='Normalize')}
 guarded=choose(old,relation(physical_step(item,physical),logical_step(item,logical)),yes)
 step_id=add('indexed_step_simulates',dict(physical=s,logical=ls,item=u),guarded,yes,step_proof,[insert_id,direction_id,witness_id,absence_id,names['all_monotone'],names['member_append_u32'],names['coverage_insert_u32'],names['coverage_append_u32']])
 initial=op(s,'record:'+builder,op(m,'local:map-empty'),op(buf,'local:buffer-empty'))
 physical_callback=lam(u,lam(s,physical_step(bound(u,1),bound(s,0))))
 logical_callback=component['insert_step']
 relate=lam(s,lam(ls,relation(bound(s,1),bound(ls,0))))
 args=dict(xs=xs,physical=initial,logical=nil,physical_step=physical_callback,logical_step=logical_callback,relate=relate)
 sim_id=names['foldl_simulates'];sim_from,_=instance(sim_id,args,{'A':'U32','P':s['Value'],'L':ls['Value']})
 p=var(s,'__assumed_p');l=var(ls,'__assumed_l');key=var(u,'__assumed_item')
 step_args=dict(physical=p,logical=l,item=key);step_from,_=instance(step_id,step_args)
 assumption=trans(step_from,'Normalize',use(step_id,step_args))
 folded=op(s,'call:foldl',xs,initial,physical_callback);expected=op(ls,'call:foldl',xs,nil,logical_callback)
 simulated=relation(folded,expected)
 folded_id=add('indexed_construct_simulates',dict(xs=ls),simulated,yes,trans(sim_from,'Normalize',use(sim_id,args,{'A':'U32','P':s['Value'],'L':ls['Value']},[assumption])),[step_id,sim_id])
 equality=eq(output(folded),expected)
 observation={'Cases':dict(condition=equality,on_true='Normalize',on_false=trans(simulated,'Normalize',use(folded_id,dict(xs=xs))))}
 final=add('indexed_construct_equivalent',dict(xs=ls),output(folded),expected,assert_true(equality,observation,'Normalize'),[folded_id])
 return dict(objects=objects,names=names,equivalence=final)

def author(compiler,source,directory):
 from producers.set_contracts import derive as prefix
 from producers.beta_specialization15 import beta_normalize
 D=Path(directory).resolve();D.mkdir(parents=True,exist_ok=True)
 compiler=Path(compiler).resolve();source=Path(source).resolve();libraries=Path(__file__).resolve().parents[1]/'libraries'
 framework=D/'framework';framework.mkdir(exist_ok=True)
 for stem,file in [('storage','storage-observations.ink'),('local','local-relations.ink'),('general','general-laws.ink'),('filter','sequence-filter-laws.ink')]:
  r=subprocess.run([str(compiler),'emit-laws',str(libraries/file),'-o',str(framework/(stem+'-laws.json'))],check=True,capture_output=True,text=True)
  (framework/(stem+'-laws.log')).write_text(r.stdout)
 (D/'empty.ink').write_text('module Unrelated;fn same(x:u32)->u32{return x;}')
 empty=D/'empty.core.json';subprocess.run([str(compiler),'emit-core',str(D/'empty.ink'),'-o',str(empty)],check=True,capture_output=True,text=True)
 obligations=D/'obligations.json';subprocess.run([str(compiler),'emit-contract-obligations',str(source),'-o',str(obligations)],check=True,capture_output=True,text=True)
 context=json.loads(obligations.read_text())['definition_context']
 scans=[]
 for name,record in context['definitions'].items():
  d=record['definition'];result=d['result']
  if isinstance(result,dict)and 'Named'in result and dict(context['records'].get(result['Named'],[]))=={'seen':{'List':'U32'},'valid':'Bool'}:
   if beta_normalize(d['body'])['node'].get('Op',[None])[0]=='call:foldl':scans.append(name)
 if len(scans)!=1:raise ValueError('expected one structural u32 logical scan')
 component=prefix(compiler,context,D/'prefix',framework,empty,scans[0])
 candidates=[]
 for builder,fields in context['records'].items():
  if dict(fields)!={'seen':{'Map':['U32','Bool']},'out':{'Buffer':'U32'}}:continue
  steps=[name for name,r in context['definitions'].items()if [t for _,t in r['definition']['params']]==['U32',{'Named':builder}]and r['definition']['result']=={'Named':builder}]
  if len(steps)==1:candidates.append((builder,steps[0]))
 if len(candidates)!=1:raise ValueError('expected one structural indexed construction proposal')
 result=derive(compiler,context,component,D/'equivalence',empty,*candidates[0])
 bank=Store.publish(D/'proofs',result['objects'].values(),result['names']);bundle=bank.bundle([result['equivalence']])
 (D/'equivalence.json').write_text(json.dumps(bundle,separators=(',',':'))+'\n')
 return result,bank

if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('source');parser.add_argument('output');parser.add_argument('--compiler',required=True)
 args=parser.parse_args();result,bank=author(args.compiler,args.source,args.output)
 print(json.dumps(dict(status='checked',equivalence=result['equivalence'],objects=len(bank.bundle([result['equivalence']])['objects']),snapshot=bank.snapshot_id)))
