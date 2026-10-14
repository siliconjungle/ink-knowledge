"""Untrusted decomposition of small record mutators into field helpers.

The source extension and every complete-record equality replay independently.
No tree, CRDT, field name, workload or theorem identifier grants authority.
"""
import copy,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import Store,canonical,entry,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from producers.definition_context28 import bind
from producers.semantic_laws import law,op,value,var

def candidates(core,limit=16):
 records=core['program']['records'];functions=core['program']['functions'];result=[]
 def immutable(t,active=frozenset()):
  if isinstance(t,str):return True
  if not isinstance(t,dict):return False
  if 'Named'in t:
   n=t['Named'];return n not in active and n in records and all(immutable(v,active|{n})for _,v in records[n])
  if 'List'in t or 'Option'in t:return immutable(next(iter(t.values())),active)
  if 'Result'in t:return all(immutable(v,active)for v in t['Result'])
  return False
 for f in functions:
  if len(result)>=limit:break
  ty=f['result'];owners=[n for n,t in f['params']if t==ty]
  if not isinstance(ty,dict)or 'Named'not in ty or ty['Named']not in records or len(owners)!=1:continue
  fields=records[ty['Named']];schema=dict(fields);root=owners[0]
  try:
   if len(fields)<2 or len(canonical(f['body']))>8192:continue
   changed=set();names={n for n,_ in f['params']}
   def leaves(e):
    if 'Let'in e:
     n,_,_,body=e['Let'];names.add(n)
     if n==root:raise ValueError('shadowed owner')
     leaves(body)
    elif 'Call'in e and e['Call'][0]=='choose':
     for branch in e['Call'][1][1:]:leaves(branch)
    elif e=={'Var':root}:pass
    elif 'Record'in e and e['Record'][0]==ty['Named']:
     for n,v in e['Record'][1]:
      if v!={'Field':[{'Var':root},n]}:changed.add(n)
    else:raise ValueError('unsupported result flow')
   leaves(f['body'])
   if len(changed)!=1:continue
   changed=next(iter(changed));observations={}
   def field(n):
    if n not in schema:raise ValueError('unknown field')
    if n not in observations:
     fresh='frame_field_'+str(len(observations))
     while fresh in names:fresh+='_'
     names.add(fresh);observations[n]=fresh
    return {'Var':observations[n]}
   def expression(e):
    if 'Field'in e and e['Field'][0]=={'Var':root}:return field(e['Field'][1])
    if e=={'Var':root}:raise ValueError('whole owner observation')
    if 'Lambda'in e:raise ValueError('callback outside bounded family')
    if 'Let'in e:
     n,annotation,initial,body=e['Let'];names.add(n)
     if n==root:raise ValueError('shadowed owner')
     return {'Let':[n,annotation,expression(initial),expression(body)]}
    def walk(v):
     if isinstance(v,dict):return expression(v)
     if isinstance(v,list):return [walk(x)for x in v]
     return copy.deepcopy(v)
    return {n:walk(v)for n,v in e.items()}
   def body(e):
    if 'Let'in e:
     n,annotation,initial,rest=e['Let'];return {'Let':[n,annotation,expression(initial),body(rest)]}
    if 'Call'in e and e['Call'][0]=='choose':
     condition,yes,no=e['Call'][1];return {'Call':['choose',[expression(condition),body(yes),body(no)]]}
    if e=={'Var':root}:return field(changed)
    if 'Record'in e:return expression(dict(e['Record'][1])[changed])
    raise ValueError('unsupported result flow')
   projected=body(f['body'])
   if any(n!=changed and not immutable(schema[n])for n in observations):continue
   signature=[];arguments=[]
   for n,t in f['params']:
    if n!=root:signature.append([n,t]);arguments.append({'Var':n})
    else:
     for name in observations:
      signature.append([observations[name],schema[name]]);arguments.append({'Field':[{'Var':root},name]})
   helper=dict(name='frame_projected_'+identity(dict(function=f,changed=changed,observations=observations))[:20],params=signature,result=schema[changed],body=projected)
   if any(g['name']==helper['name']for g in functions):continue
   result.append(dict(original=f,helper=helper,arguments=arguments,root=root,changed=changed))
  except (ValueError,KeyError):continue
 return result

def propose(context,limit=16):
 if context.get('representation'):return
 core=context['core'];rows=candidates(core,limit)
 if not rows:return
 root=Path(context['knowledge_root']);store=Store(root,root/'store/snapshots'/(context['knowledge_snapshot']+'.json'))
 compiler=context['compiler']
 def invoke(*args):
  r=subprocess.run([compiler,*map(str,args)],capture_output=True,text=True,timeout=context.get('check_timeout',120))
  if r.returncode:raise ValueError(r.stderr[-2000:])
  return json.loads(r.stdout)if r.stdout.lstrip().startswith(('{','['))else r.stdout
 with tempfile.TemporaryDirectory(prefix='ink-frame-projection-')as temporary:
  d=Path(temporary);original=d/'original.json';original.write_bytes(canonical(core))
  extension=entry('definition','ink-source-extension-v1',dict(functions=[r['helper']for r in rows],records={},enums={},ids=[]));eid=identity(extension)
  request=dict(schema=1,semantics='ink-source-extension-v1',input_core_sha256=context['source'],extension=eid,knowledge=ProposalViews(store,{eid:extension},d/'extension').bundle([eid]))
  req=d/'extension.json';req.write_bytes(canonical(request));extended=d/'extended.json'
  receipt=invoke('extend-core',original,req,'--core','-o',extended);program=json.loads(extended.read_bytes())
  semantic=d/'semantic.json';invoke('emit-semantic',extended,'--core','-o',semantic);subject=json.loads(semantic.read_bytes())
  from ink_planner.semantic_search import positions,match
  for row in rows:
   f,h=row['original'],row['helper'];env=dict(f['params']);owner=var(value(env[row['root']]),row['root'])
   def term(e):
    if 'Var'in e:return var(value(env[e['Var']]),e['Var'])
    base,n=e['Field'];t=term(base);ty=dict(core['program']['records'][t['sort']['Value']['Named']])[n]
    return op(value(ty),'field:'+n,t)
   def proof(t):
    node=t['node']
    if isinstance(node,dict)and node.get('Op',[None])[0]=='call:choose':
     condition,yes,no=node['Op'][1]
     if not any(isinstance(x['node'],dict)and'Bound'in x['node']for _,x in positions(condition)):
      return {'Cases':dict(condition=condition,on_true=proof(yes),on_false=proof(no))}
    return 'Normalize'
   try:
    left=op(value(f['result']),'call:'+f['name'],*(var(value(t),n)for n,t in f['params']))
    updated=op(value(h['result']),'call:'+h['name'],*(term(e)for e in row['arguments']))
    fields=[updated if n==row['changed']else op(value(t),'field:'+n,owner)for n,t in core['program']['records'][f['result']['Named']]]
    right=op(value(f['result']),'record:'+f['result']['Named'],*fields)
    theorem=bind(law({n:value(t)for n,t in f['params']},left,right,proof(subject['functions'][f['name']])),program,subject,[f['name'],h['name']])
    obj=semantic_entry(theorem);lid=identity(obj);view=ProposalViews(store,{lid:obj},d/'law').bundle([lid]);applications=[]
    def lexical(t):
     node=t['node']
     return isinstance(node,dict)and(bool(set(node)&{'Free','Bound'})or('Op'in node and node['Op'][0].startswith('field:')and len(node['Op'][1])==1 and lexical(node['Op'][1][0])))
    for name,b in subject['functions'].items():
     if name==h['name']:continue
     for path,target in positions(b):
      node=target['node'];call=node.get('Op')if isinstance(node,dict)else None
      if not call or call[0]!='call:'+f['name']:continue
      actual=call[1][next(i for i,(n,_)in enumerate(f['params'])if n==row['root'])]
      if not lexical(actual):continue
      arguments={}
      if match(left,target,theorem['params'],arguments):applications.append(dict(function=name,path=list(path),law=lid,arguments=arguments,premises=[]))
    if not applications:continue
    packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=receipt['core_sha256'],knowledge=view,applications=applications)
    yield dict(status='proposal',label='frame-projection/'+f['name'],steps=[dict(kind='extension',package=request),dict(kind='rewrite',package=packet)])
   except (ValueError,KeyError,TypeError)as error:yield dict(status='declined',label='frame-projection/'+f['name'],reason=str(error))
