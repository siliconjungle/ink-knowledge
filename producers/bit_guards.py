"""Discover constant unsigned scalar guards with independently replayed RUP.

Application names, profiles and labels supply no premises. Local binders become
quantified parameters, then bind back to the exact source site during replay.
"""
import copy,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from producers.definition_context28 import bind
from producers.semantic_laws import law,value,var,term
from producers.bitvector_proofs import certificate

def candidates(subject,core,limit=16):
 from ink_planner.semantic_search import children
 functions={f['name']:f for f in core['program']['functions']};seen=set();rows=[]
 def walk(t,path,scope,name):
  if len(rows)>=limit:return
  node=t['node'];call=node.get('Op')if isinstance(node,dict)else None
  if call and call[0]=='call:choose' and len(call[1])==3:
   condition=call[1][0]
   # A bounded discovery family; the kernel still proves each complete guard.
   raw=canonical(condition)
   if len(raw)<=8192 and b'"Word"'in raw and condition['sort']==value('Bool'):
    env={n:value(ty)for n,ty in functions[name]['params']};arguments={n:var(s,n)for n,s in env.items()}
    used={};fresh=set(env)
    def opened(t,depth=0):
     n=t['node']
     if isinstance(n,dict)and'Bound'in n and n['Bound']>=depth:
      index=n['Bound']-depth
      if index>=len(scope):raise ValueError('missing guard binder')
      if index not in used:
       label='guard_local_'+str(index)
       while label in fresh:label+='_'
       fresh.add(label);used[index]=label;env[label]=scope[-index-1];arguments[label]=term(scope[-index-1],{'Bound':index})
      return var(env[used[index]],used[index])
     out=copy.deepcopy(t)
     if isinstance(n,dict)and'Lambda'in n:out['node']['Lambda']=opened(n['Lambda'],depth+1)
     elif isinstance(n,dict)and'Op'in n:out['node']['Op'][1]=[opened(c,depth)for c in n['Op'][1]]
     elif isinstance(n,dict)and'Cons'in n:out['node']['Cons']=[opened(c,depth)for c in n['Cons']]
     return out
    try:
     guard=opened(condition);key=identity(dict(guard=guard,params=env))
     if key not in seen:seen.add(key);rows.append(dict(function=name,path=list(path)+( [0] ),guard=guard,params=env,arguments=arguments))
    except (ValueError,KeyError):pass
  for i,c in enumerate(children(t)):
   inner=scope+[t['sort']['Arrow'][0]]if isinstance(node,dict)and'Lambda'in node else scope
   walk(c,path+[i],inner,name)
 for name,t in subject['functions'].items():walk(t,[],[],name)
 return rows

def propose(context,limit=16,seconds=2):
 if context.get('representation'):return
 core=context['core'];root=Path(context['knowledge_root']);store=Store(root,root/'store/snapshots'/(context['knowledge_snapshot']+'.json'))
 compiler=context['compiler'];timeout=context.get('check_timeout',120)
 def invoke(*args):
  r=subprocess.run([compiler,*map(str,args)],capture_output=True,text=True,timeout=timeout)
  if r.returncode:raise ValueError(r.stderr[-2000:])
  return r
 with tempfile.TemporaryDirectory(prefix='ink-bit-guards-')as td:
  d=Path(td);source=d/'core.json';source.write_bytes(canonical(core));semantic=d/'semantic.json';invoke('emit-semantic',source,'--core','-o',semantic);subject=json.loads(semantic.read_bytes())
  for row in candidates(subject,core,limit):
   admitted=False
   for truth in [False,True]:
    try:
     goal=dict(params=row['params'],conditions=[],**{'from':row['guard'],'to':term(value('Bool'),{'Bool':truth})})
     request=d/'goal.json';request.write_bytes(canonical(goal));cnf=d/'cnf.json';invoke('semantic-bitvector-obligation',source,request,'--core','-o',cnf)
     proof=certificate(json.loads(cnf.read_bytes()),seconds=seconds,conflicts=10000)
     theorem=bind(law(row['params'],goal['from'],goal['to'],dict(BitVector=dict(hypotheses=[],certificate=proof))),core,subject)
     obj=semantic_entry(theorem);lid=identity(obj);view=ProposalViews(store,{lid:obj},d/'view').bundle([lid])
     packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=context['source'],knowledge=view,applications=[dict(function=row['function'],path=row['path'],law=lid,arguments=row['arguments'],premises=[])])
     yield dict(status='proposal',label='bit-guard/'+row['function'],steps=[dict(kind='rewrite',package=packet)]);admitted=True;break
    except (ValueError,KeyError,TypeError,subprocess.TimeoutExpired):continue
   if not admitted:yield dict(status='declined',label='bit-guard/'+row['function'],reason='No checked constant-guard certificate within discovery budget')
