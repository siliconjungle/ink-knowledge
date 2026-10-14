"""Bounded source unfolding choices for large carriers and small helpers.

Carrier size and call counts order proposals only. Every complete definition
equality and source application must be replayed; names confer no authority.
"""
import json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from producers.definition_context28 import bind
from producers.semantic_laws import law,op,value,var

def candidates(core,subject,limit=8,max_body=64,max_applications=32,min_body=1,frequencies=None):
 from ink_planner.semantic_search import children,positions,match
 if limit<1 or max_body<1 or min_body<1 or max_applications<1:return
 records=core['program']['records'];functions=core['program']['functions']
 def owned(t,seen=frozenset()):
  if isinstance(t,list):return any(owned(x,seen)for x in t)
  if not isinstance(t,dict):return False
  if 'Buffer'in t or 'Map'in t:return True
  if 'Named'in t:
   name=t['Named']
   return name not in seen and any(owned(x,seen|{name})for _,x in records.get(name,[]))
  return any(owned(x,seen)for x in (t.get('Result',[])if 'Result'in t else t.values()))
 def words(t,seen=frozenset()):
  if isinstance(t,str):return 3 if t=='String' else 1
  if not isinstance(t,dict):return 0
  if 'Named'in t:
   name=t['Named']
   if name in seen:return 1
   total=0
   for _,x in records.get(name,[]):
    total+=words(x,seen|{name})
    if total>=256:return 256
   return total
  if 'Buffer'in t or 'Map'in t or 'List'in t:return 3
  return 1
 def size(t):
  pending=[t];count=0
  while pending:
   count+=1
   if count>max_body:return count
   pending.extend(children(pending.pop()))
  return count
 calls={}
 for name,body in subject['functions'].items():
  for path,t in positions(body):
   node=t['node'];call=node.get('Op')if isinstance(node,dict)else None
   if call and call[0].startswith('call:'):calls.setdefault(call[0][5:],[]).append((name,path,t))
 ranked=[]
 for f in functions:
  name=f['name'];body=subject['functions'].get(name);sites=calls.get(name,[])
  if body is None or not sites or any(caller==name for caller,_,_ in sites):continue
  count=size(body);carrier=max([words(f['result']),*[words(t)for _,t in f['params']]])
  if count<min_body or count>max_body or carrier<6:continue
  # Constructor/fallback call counts overstate hot work. Existing immutable
  # parameter loans also remove some transfer costs. Prefer helpers that
  # receive affine carriers, without treating that estimate as profitability.
  affine=any(owned(t)for _,t in f['params'])
  ranked.append((affine,carrier,count,name,f,body,sites))
 # Recorded calls guide proposal order only. Missing observations keep the
 # structural estimate; every proposed equality and measured choice still
 # passes the usual independent gates.
 frequencies=frequencies or {}
 profiled=any('call:'+row[3] in frequencies for row in ranked)
 ranked=[(0 if profiled else -int(affine),-carrier*frequencies.get('call:'+name,len(sites))/max(1,count),name,f,body,sites)
         for affine,carrier,count,name,f,body,sites in ranked]
 for _,_,name,f,body,sites in sorted(ranked)[:limit]:
  params={n:value(t)for n,t in f['params']}
  source=op(value(f['result']),'call:'+name,*(var(params[n],n)for n,_ in f['params']))
  theorem=bind(law(params,source,body),core,subject,[name]);obj=semantic_entry(theorem);lid=identity(obj)
  applications=[]
  # A single call per caller keeps paths independent, bounds source growth and
  # permits later planner states to revisit the same family compositionally.
  callers=set()
  for caller,path,t in sites:
   if caller in callers:continue
   args={}
   if not match(theorem['from'],t,set(params),args):continue
   applications.append(dict(function=caller,path=list(path),law=lid,arguments=args,premises=[]));callers.add(caller)
   if len(applications)>=max_applications:break
  if applications:yield dict(name=name,object=obj,law=lid,applications=applications)

def propose(context,limit=8,max_body=64,max_applications=32,physical_strategies=(),scoped_strategies=(),min_body=1):
 if context.get('representation'):return
 core=context['core'];root=Path(context['knowledge_root']);store=Store(root,root/'store/snapshots'/(context['knowledge_snapshot']+'.json'))
 with tempfile.TemporaryDirectory(prefix='ink-small-inline-')as temporary:
  d=Path(temporary);source=d/'core.json';source.write_bytes(canonical(core));semantic=d/'semantic.json'
  result=subprocess.run([context['compiler'],'emit-semantic',str(source),'--core','-o',str(semantic)],capture_output=True,text=True,timeout=context.get('check_timeout',120))
  if result.returncode:raise ValueError(result.stderr[-2000:])
  subject=json.loads(semantic.read_bytes())
  for row in candidates(core,subject,limit,max_body,max_applications,min_body,context.get('frequencies')):
   view=ProposalViews(store,{row['law']:row['object']},d/row['law']).bundle([row['law']])
   packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=context['source'],knowledge=view,applications=row['applications'])
   if (physical_strategies or scoped_strategies) and context.get('emit_target','rust')in {'rust','rust-wasm'}:
    # Complete source/layout combinations before a broad frontier consumes its
    # state limit. These remain distinct, measured alternatives. The rewritten
    # source and every fresh physical capability replay independently.
    plan=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=context['source'],steps=[dict(kind='rewrite',package=packet)])
    checked=subprocess.run([context['compiler'],'plan-session',str(source),'--target',context.get('emit_target','rust')],input=canonical(plan).decode()+'\n',capture_output=True,text=True,timeout=context.get('check_timeout',120))
    receipts=[json.loads(line)for line in checked.stdout.splitlines()]
    result=next((r for r in receipts if r.get('status')=='checked'),None)
    if checked.returncode or result is None:
     yield dict(status='declined',label='small-inline-layout/'+row['name'],reason=checked.stderr[-2000:]or str(receipts[-1:]))
    else:
     state=result['state']
     from producers.planning_recipes import physical
     updated=dict(context,core=state['core'],source=state['source'],physical=None,representation=None)
     choices=list(physical(updated,physical_strategies,[]))
     if scoped_strategies:
      from producers.readonly_borrows import scoped_candidates
      # The source rewrite invalidates every old lexical capability. Derive
      # fresh sites from the checked result rather than rehashing old metadata.
      choices.extend(scoped_candidates(updated,scoped_strategies))
     for choice in choices:
      if choice['step']['package']['buffers']=='scoped'and not choice['step']['package']['borrow_reads']:continue
      yield dict(status='proposal',label='small-inline-layout/'+row['name']+'/'+choice['label'],steps=[dict(kind='rewrite',package=packet),choice['step']])
   yield dict(status='proposal',label='small-inline/'+row['name'],step=dict(kind='rewrite',package=packet))
