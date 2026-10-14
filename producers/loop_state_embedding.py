"""Propose source loop-state narrowing with checked embedding simulations.

This is untrusted proof construction, not a compiler loop recognizer. The exact
source functions, callback simulation, stop predicate and output all replay in
the ordinary equality kernel. No well-formedness assumption is invented.
"""
from producers.definitional_roundtrips import _beta,_substitute
from producers.definition_context28 import bind
from producers.semantic_laws import law,value,var,op,word,lam,bound,term
from ink_planner.semantic_search import children,map_children
from producers.definitional_roundtrips import _shift

def propose(core,subject,left,right,embedding_law,*,conditions=(),budget=16000):
 functions={f['name']:f for f in core['program']['functions']};records=core['program']['records'];remaining=[budget]
 declaration=functions[left];other=functions[right]
 if declaration['params']!=other['params']or declaration['result']!=other['result']:raise ValueError('source signatures differ')
 def trans(m,l,r):return {'Trans':dict(middle=m,left=l,right=r)}
 def call(t):return t['node'].get('Op')if isinstance(t['node'],dict)else None
 def reduce(t):
  remaining[0]-=1
  if remaining[0]<0:raise ValueError('source embedding proposal work limit')
  # Keep callbacks opaque until applied to the quantified simulation state.
  # Proof terms under a lambda require the kernel's fresh lexical binder;
  # carrying raw de Bruijn indices into a Trans middle would be ill-scoped.
  if isinstance(t['node'],dict)and'Lambda'in t['node']:return t,'Normalize'
  c=call(t);after=None
  if c:
   name,args=c
   if name.startswith('call:')and name[5:]in functions:
    f=functions[name[5:]];after=_substitute(subject['functions'][f['name']],dict(zip((n for n,_ in f['params']),args)))
   elif name=='apply'and isinstance(args[0]['node'],dict)and'Lambda'in args[0]['node']:after=_beta(args[0]['node']['Lambda'],args[1])
   elif name.startswith('field:'):
    rc=call(args[0])
    if rc and rc[0].startswith('record:'):
     i=next(i for i,(field,_)in enumerate(records[rc[0][7:]])if field==name[6:]);after=rc[1][i]
   if after is not None:
    result,proof=reduce(after);return result,trans(after,'Unfold',proof)
  if c and c[0]=='call:choose':
   condition,cp=reduce(c[1][0])
   for i,premise in enumerate(conditions):
    if condition==premise['from']and'Bool'in premise['to']['node']:
     normalized=op(t['sort'],c[0],condition,*c[1][1:]);literal=op(t['sort'],c[0],premise['to'],*c[1][1:]);selected=c[1][1 if premise['to']['node']['Bool']else 2]
     result,tail=reduce(selected)
     branch=trans(literal,{'Congruence':[{'Hypothesis':i},'Normalize','Normalize']},trans(selected,'Unfold',tail))
     return result,trans(normalized,{'Congruence':[cp,'Normalize','Normalize']},branch)
  parts=[reduce(x)for x in children(t)]
  if not parts:return t,'Normalize'
  iterator=iter(x for x,_ in parts);middle=map_children(t,lambda _:next(iterator));proof={'Congruence':[p for _,p in parts]}
  c=call(middle)
  if c:
   name,args=c
   if name=='call:choose':
    for i,premise in enumerate(conditions):
     if args[0]==premise['from']and'Bool'in premise['to']['node']:
      literal=op(middle['sort'],name,premise['to'],args[1],args[2]);selected=args[1 if premise['to']['node']['Bool']else 2]
      result,tail=reduce(selected)
      branch=trans(literal,{'Congruence':[{'Hypothesis':i},'Normalize','Normalize']},trans(selected,'Unfold',tail))
      return result,trans(middle,proof,branch)
   if name.startswith('record:')and args:
    projections=[call(x)for x in args];fields=records[name[7:]]
    if len(args)==len(fields)and all(p and p[0]=='field:'+field for p,(field,_)in zip(projections,fields)):
     receiver=projections[0][1][0]
     if receiver['sort']==middle['sort']and all(p[1]==[receiver]for p in projections):return receiver,trans(middle,proof,'Normalize')
   if(name=='apply'and isinstance(args[0]['node'],dict)and'Lambda'in args[0]['node'])or(name.startswith('field:')and(call(args[0])or[''])[0].startswith('record:')):
    result,tail=reduce(middle);return result,trans(middle,proof,tail)
  return middle,proof
 params={n:value(t)for n,t in declaration['params']};args=[var(params[n],n)for n,_ in declaration['params']]
 source=op(value(declaration['result']),'call:'+left,*args);target=op(source['sort'],'call:'+right,*args)
 a,ap=reduce(source);b,bp=reduce(target)
 if a==b:
  result=law(params,source,target,trans(a,ap,{'Sym':bp}),conditions=list(conditions));result['semantics']='ink-general-laws-v1'
  return bind(result,core,subject,[left,right])
 def loops(t):
  c=call(t)
  if c and c[0]=='call:repeat_until':return [t]
  return [v for child in children(t)for v in loops(child)]
 old_loops=loops(a);new_loops=loops(b)
 if not old_loops or not new_loops:raise ValueError('both sources must contain a loop')
 old=old_loops[0];new=new_loops[0]
 if any(x!=old for x in old_loops)or any(x!=new for x in new_loops):raise ValueError('one distinct loop per source required')
 count,initial,stop,step=call(old)[1];small_count,small_initial,small_stop,small_step=call(new)[1]
 if count!=small_count:raise ValueError('iteration bounds differ')
 old_ctor=call(initial);new_ctor=call(small_initial)
 if not old_ctor or not new_ctor or not old_ctor[0].startswith('record:')or not new_ctor[0].startswith('record:'):raise ValueError('record initial states required')
 def image(old_sort,new_value,old_initial):
  old_name=old_sort['Value'].get('Named')if isinstance(old_sort.get('Value'),dict)else None
  new_name=new_value['sort']['Value'].get('Named')if isinstance(new_value['sort'].get('Value'),dict)else None
  if old_name not in records or new_name not in records:raise ValueError('nested embedding requires records')
  new_fields=dict(records[new_name]);values=[]
  for field,ty in records[old_name]:
   captured=op(value(ty),'field:'+field,old_initial)
   if field not in new_fields:values.append(captured);continue
   projected=op(value(new_fields[field]),'field:'+field,new_value)
   if ty==new_fields[field]:values.append(projected)
   elif isinstance(ty,dict)and'Named'in ty and isinstance(new_fields[field],dict)and'Named'in new_fields[field]:values.append(image(value(ty),projected,captured))
   else:raise ValueError('retained field type differs')
  return op(old_sort,'record:'+old_name,*values)
 embed=lam(small_initial['sort'],image(initial['sort'],bound(small_initial['sort'],0),_shift(initial,1)))
 app=lambda f,x:op(f['sort']['Arrow'][1],'apply',f,x)
 current=var(small_initial['sort'],'__assumed_current');item=var(value('U32'),'__assumed_item')
 # The callbacks have been definitionally expanded, so exact beta/projection
 # computation suffices for both universally quantified simulation premises.
 before=app(app(step,item),app(embed,current));after=app(embed,app(app(small_step,item),current))
 x,xp=reduce(before);y,yp=reduce(after)
 if x!=y:raise ValueError('callback does not preserve captured state')
 transition=trans(x,xp,{'Sym':yp})
 before=app(stop,app(embed,current));after=app(small_stop,current)
 x,xp=reduce(before);y,yp=reduce(after)
 if x!=y:raise ValueError('stop predicate differs on embedded states')
 stopping=trans(x,xp,{'Sym':yp})
 zero=word('U32',0)
 large_run=op(initial['sort'],'until.from',count,zero,app(embed,small_initial),stop,step)
 small_run=op(small_initial['sort'],'until.from',count,zero,small_initial,small_stop,small_step)
 image=app(embed,small_run)
 use={'Use':dict(law=embedding_law,types=dict(State=initial['sort']['Value'],Reduced=small_initial['sort']['Value']),arguments=dict(count=count,index=zero,state=small_initial,embed=embed,stop=stop,reduced_stop=small_stop,step=step,reduced_step=small_step),premises=[],assumptions=[transition,stopping])}
 replacement=app(embed,new)
 original_run=op(initial['sort'],'until.from',count,zero,initial,stop,step)
 loop_proof=trans(original_run,'Unfold',trans(large_run,{'Congruence':['Normalize']*5},trans(image,use,{'Congruence':['Normalize',{'Sym':'Unfold'}]})))
 def rewrite(t):
  if t==old:return replacement,loop_proof
  parts=[rewrite(x)for x in children(t)]
  if not parts:return t,'Normalize'
  iterator=iter(x for x,_ in parts);return map_children(t,lambda _:next(iterator)),{'Congruence':[p for _,p in parts]}
 rewritten,rp=rewrite(a);normal,np=reduce(rewritten);wanted,wp=reduce(b)
 if normal!=wanted:raise ValueError('output differs after loop simulation')
 proof=trans(a,ap,trans(rewritten,rp,trans(normal,np,trans(b,{'Sym':wp},{'Sym':bp}))))
 result=law(params,source,target,proof,conditions=list(conditions),dependencies=[embedding_law]);result['semantics']='ink-general-laws-v1'
 return bind(result,core,subject,[left,right])

def guarded_proposals(core,subject,left,right,key):
 """Prove both branches of an existing source guard using ordinary laws."""
 from ink_knowledge import identity,semantic_entry
 functions={f['name']:f for f in core['program']['functions']};records=core['program']['records']
 def call(t):return t['node'].get('Op')if isinstance(t['node'],dict)else None
 def one(t):
  c=call(t)
  if not c:return None
  name,args=c
  if name.startswith('call:')and name[5:]in functions:
   f=functions[name[5:]];return _substitute(subject['functions'][f['name']],dict(zip((n for n,_ in f['params']),args)))
  if name=='apply'and isinstance(args[0]['node'],dict)and'Lambda'in args[0]['node']:return _beta(args[0]['node']['Lambda'],args[1])
  if name.startswith('field:'):
   c=call(args[0])
   if c and c[0].startswith('record:'):
    i=next(i for i,(field,_)in enumerate(records[c[0][7:]])if field==name[6:]);return c[1][i]
  return None
 def calculate(t,depth=0):
  if depth>96:raise ValueError('predicate discovery depth')
  after=one(t)
  if after is not None:return calculate(after,depth+1)
  c=call(t)
  if not c:return t
  result=op(t['sort'],c[0],*(calculate(x,depth+1)for x in c[1]));after=one(result)
  return calculate(after,depth+1)if after is not None else result
 declaration=functions[left];params={n:value(t)for n,t in declaration['params']};args=[var(params[n],n)for n,_ in declaration['params']]
 source=op(value(declaration['result']),'call:'+left,*args);target=op(source['sort'],'call:'+right,*args);current=target
 for _ in range(64):
  c=call(current)
  if c and c[0]=='call:choose':break
  current=one(current)
  if current is None:raise ValueError('replacement has no outer source guard')
 else:raise ValueError('guard discovery budget')
 guard=calculate(call(current)[1][0]);objects={};proofs={};names={}
 for truth in [False,True]:
  branch=propose(core,subject,left,right,key,conditions=[dict(**{'from':guard,'to':term(value('Bool'),{'Bool':truth})})]);obj=semantic_entry(branch);ident=identity(obj);objects[ident]=obj;names['branch_'+str(truth).lower()]=ident
  proofs[truth]={'Use':dict(law=ident,arguments={n:var(t,n)for n,t in params.items()},premises=[{'Hypothesis':0}])}
 result=law(params,source,target,{'Cases':dict(condition=guard,on_false=proofs[False],on_true=proofs[True])},dependencies=list(names.values()));result=bind(result,core,subject,[left,right]);obj=semantic_entry(result);ident=identity(obj);objects[ident]=obj;names['guarded_loop_embedding']=ident
 return objects,ident

def candidates(context,limit=4,max_applications=64):
 """Discover smaller source loop states, prove them, and propose all call sites.

 The state-size heuristic only orders proposals; source equality is mandatory.
 Existing ordinary source alternatives supply executable helpers. No program,
 function or record names determine applicability or grant rewrite authority.
 """
 import json,subprocess,tempfile
 from pathlib import Path
 from ink_knowledge import Store,canonical,identity,semantic_entry
 from ink_planner.semantic_search import positions,match
 root=Path(__file__).resolve().parents[1]
 # A cheap syntactic prescan avoids semantic elaboration when no pair of
 # ordinary source loops has a smaller carrier. This orders discovery only.
 records=context['core']['program']['records']
 def words(ty,seen=frozenset()):
  if isinstance(ty,str):return 3 if ty=='String'else 1
  if not isinstance(ty,dict):return 1
  if any(k in ty for k in ['List','Buffer','Map']):return 3
  name=ty.get('Named')
  if name in records and name not in seen:return min(256,sum(words(t,seen|{name})for _,t in records[name]))
  return 1
 possible={}
 def initial_states(v):
  if isinstance(v,dict):
   c=v.get('Call')
   if c and c[0]=='repeat_until'and len(c[1])==4:
    initial=c[1][1].get('Record')if isinstance(c[1][1],dict)else None
    if initial and initial[0]in records:yield words({'Named':initial[0]})
   for x in v.values():yield from initial_states(x)
  elif isinstance(v,list):
   for x in v:yield from initial_states(x)
 for f in context['core']['program']['functions']:
  sizes=list(initial_states(f['body']))
  if len(sizes)==1:possible.setdefault(canonical(dict(params=f['params'],result=f['result'])).decode(),set()).add(sizes[0])
 if not any(len(sizes)>1 for sizes in possible.values()):return
 parent=Store(root/'libraries/proofs/until-embedding')
 key=__import__('json').loads((parent.root/'store/names.json').read_text())['until_embedding']
 with tempfile.TemporaryDirectory(prefix='ink-loop-embedding-')as temporary:
  d=Path(temporary);corefile=d/'core.json';corefile.write_bytes(canonical(context['core']));subjectfile=d/'subject.json'
  r=subprocess.run([context['compiler'],'emit-semantic',corefile,'--core','-o',subjectfile],capture_output=True,text=True,timeout=context.get('check_timeout',120))
  if r.returncode:
   yield dict(status='declined',label='loop-state embedding',reason=r.stderr[-1500:]);return
  subject=json.loads(subjectfile.read_bytes());core=context['core'];records=core['program']['records'];groups={};sites={}
  for f in core['program']['functions']:
   name=f['name'];loop_states=[]
   for path,t in positions(subject['functions'][name]):
    c=t['node'].get('Op')if isinstance(t['node'],dict)else None
    if not c:continue
    if c[0].startswith('call:'):sites.setdefault(c[0][5:],[]).append((name,path,t))
    if c[0]=='call:repeat_until':
     sort=c[1][1]['sort'].get('Value',{});state=sort.get('Named')if isinstance(sort,dict)else None
     if state in records:loop_states.append(words({'Named':state}))
   if len(loop_states)==1:
    signature=canonical(dict(params=f['params'],result=f['result'])).decode();groups.setdefault(signature,[]).append((loop_states[0],name))
  attempted=0
  for group in groups.values():
   for old_size,left in sorted(group,reverse=True):
    if not sites.get(left):continue
    for small_size,right in sorted(group):
     if small_size>=old_size:continue
     if attempted>=limit:return
     attempted+=1
     try:
      try:
       obj=semantic_entry(propose(core,subject,left,right,key));ident=identity(obj);generated={ident:obj}
      except ValueError:
       generated,ident=guarded_proposals(core,subject,left,right,key);obj=generated[ident]
      entries={**parent.bundle([key])['objects'],**generated};view=dict(schema=1,objects=entries,roots=[ident])
      # Use the Store bundle contract, including its exact snapshot identity.
      trial=Store.publish(d/ident,list(entries.values()));view=trial.bundle([ident]);applications=[]
      for function,path,t in sites[left]:
       if function in [left,right]:continue
       arguments={}
       if match(obj['payload']['from'],t,obj['payload']['params'],arguments):applications.append(dict(function=function,path=list(path),law=ident,arguments=arguments,premises=[]))
       if len(applications)>=max_applications:break
      if applications:
       package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=context['source'],knowledge=view,applications=applications)
       yield dict(status='proposal',label='loop-state embedding/'+ident,step=dict(kind='rewrite',package=package))
     except(ValueError,KeyError,RecursionError)as e:yield dict(status='declined',label='loop-state embedding',reason=str(e)[-1500:])
