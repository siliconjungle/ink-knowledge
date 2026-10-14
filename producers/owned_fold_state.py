"""Untrusted inductive observations for source-projected owned fold helpers.

Shape discovery only proposes lemmas; every declaration, equality and use is
replayed by the existing first-order kernel. No source/hash has authority.
"""
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import normal,sub,lift

def calls(value):
 if isinstance(value,dict):
  if 'Call'in value:yield value['Call']['function']
  for child in value.values():yield from calls(child)
 elif isinstance(value,list):
  for child in value:yield from calls(child)

def candidates(objects):
 for copy,obj in list(objects.items()):
  d=obj['payload']['declaration'].get('Function')
  if not d or len(d['params'])!=1 or d['params'][0][1]!=d['result']:continue
  rows=d['result']
  if not isinstance(rows,dict)or 'Data'not in rows:continue
  datatype=objects[rows['Data']]['payload']['declaration'].get('Datatype')
  if not datatype or len(datatype['constructors'])!=2:continue
  empty,cell=datatype['constructors']
  if empty['fields']or len(cell['fields'])!=2 or cell['fields'][1]!='SelfType':continue
  item=cell['fields'][0]
  for fold in set(calls(d['body'])):
   f=objects[fold]['payload']['declaration'].get('Function')
   if not f or f['recursive']!=0 or len(f['params'])!=2 or f['params'][0][1]!=rows or f['params'][1][1]!=f['result']:continue
   acc=f['result']
   if not isinstance(acc,dict)or 'Data'not in acc:continue
   carrier=objects[acc['Data']]['payload']['declaration'].get('Datatype')
   if not carrier or len(carrier['constructors'])!=1 or carrier['constructors'][0]['fields']!=[rows]:continue
   for push in set(calls(f['body'])):
    p=objects[push]['payload']['declaration'].get('Function')
    if p and [s for _,s in p['params']]==[rows,item] and p['result']==rows:
     yield copy,fold,push,rows,item,acc

def propose(objects,add,state_proof,limit=16):
 aliases={}
 def theorem(params,a,z,proof):return add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
 for number,(copy,fold,push,rows,item,acc)in enumerate(candidates(objects)):
  if number>=limit:break
  try:
   target,copy_id=derive(objects,add,theorem,state_proof,copy,fold,push,rows,item,acc)
  except (ValueError,KeyError):continue
  aliases[copy]=(target,copy_id)
 return aliases

def derive(objects,add,theorem,state_proof,copy,fold,push,rows,item,acc):
 datatype=rows['Data']
 nil=cons(datatype,0,[]);seq=lambda h,t:cons(datatype,1,[h,t]);state=lambda xs:cons(acc['Data'],0,[xs]);observe=lambda s:{'Match':dict(scrutinee=s,branches=[dict(bindings=['observed'],body=var('observed'))])}
 concat=add({'Function':dict(params=[['xs',rows],['ys',rows]],result=rows,recursive=0,body={'Match':dict(scrutinee=var('xs'),branches=[dict(bindings=[],body=var('ys')),dict(bindings=['head','tail'],body=seq(var('head'),{'SelfCall':[var('tail'),var('ys')]}))])})})
 cat=lambda a,b:call(concat,[a,b]);xs,ys,zs=map(var,['xs','ys','zs'])
 empty_id=theorem([['xs',rows]],cat(xs,nil),xs,state_proof(objects,cat(xs,nil),xs,{'xs':rows}))
 assoc_a,assoc_z=cat(cat(xs,ys),zs),cat(xs,cat(ys,zs));assoc_id=theorem([['xs',rows],['ys',rows],['zs',rows]],assoc_a,assoc_z,state_proof(objects,assoc_a,assoc_z,dict(xs=rows,ys=rows,zs=rows)))
 push_a,push_z=call(push,[xs,var('item')]),cat(xs,seq(var('item'),nil));push_id=theorem([['xs',rows],['item',item]],push_a,push_z,state_proof(objects,push_a,push_z,dict(xs=rows,item=item)))
 R,S,H,T=map(var,['rows','state','head','tail']);a=observe(call(fold,[R,S]));z=cat(observe(S),R)
 base=trans(convert(sub(a,{'rows':nil}),observe(S)),{'Sym':{'Use':dict(theorem=empty_id,arguments=[observe(S)],premises=[])}})
 next_state=state(call(push,[observe(S),H]));start=sub(a,{'rows':seq(H,T)});finish=sub(z,{'rows':seq(H,T)})
 x1=observe(call(fold,[T,next_state]));x2=cat(observe(next_state),T);x3=cat(call(push,[observe(S),H]),T);x4=cat(cat(observe(S),seq(H,nil)),T);x5=cat(observe(S),cat(seq(H,nil),T))
 step=trans(convert(start,x1),{'GeneralizedHypothesis':dict(index=0,arguments=[next_state])},convert(x2,x3),lift({'Use':dict(theorem=push_id,arguments=[observe(S),H],premises=[])},cat(var('delta_hole'),T)),{'Use':dict(theorem=assoc_id,arguments=[observe(S),seq(H,nil),T],premises=[])},convert(x5,finish))
 proof={'GeneralizedInduction':dict(variable='rows',generalize=['state'],**{'from':a,'to':z},cases=[dict(bindings=[],proof=base),dict(bindings=['head','tail'],proof=step)])};fold_id=theorem([['rows',rows],['state',acc]],a,z,proof)
 target=add({'Function':dict(params=[['rows',rows]],result=rows,recursive=None,body=R)})
 ca,cz=call(copy,[R]),call(target,[R])
 base=convert(sub(ca,{'rows':nil}),nil);cs=sub(ca,{'rows':seq(H,T)});ce=call(target,[seq(H,T)]);next_state=state(seq(H,nil));observed=observe(call(fold,[T,next_state]));after=cat(observe(next_state),T)
 cp=trans(convert(cs,observed),{'Use':dict(theorem=fold_id,arguments=[T,next_state],premises=[])},convert(after,ce))
 copy_id=theorem([['rows',rows]],ca,cz,{'Induction':dict(variable='rows',**{'from':ca,'to':cz},cases=[dict(bindings=[],proof=base),dict(bindings=['head','tail'],proof=cp)])})
 return target,copy_id
