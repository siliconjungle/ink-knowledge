"""Propose proved ordered deduplication through generic fold observations.

The source shape only bounds discovery. Source extension, the whole fold-step
obligation and the final equality are checked independently. Whole-call measured
selection decides whether constructing the index and output buffer is worthwhile.
"""
import json,re,subprocess,tempfile
from pathlib import Path
from ink_knowledge import Store,canonical,entry,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_planner.semantic_search import children,map_children,positions,replace,shift,substitute
from producers.beta_specialization15 import beta_normalize,free_parameters
from producers.definition_context28 import bind
from producers.indexed_dedup import documents
from producers.owned_fold_contracts import closed,instantiate,lift
from producers.semantic_laws import value,var,bound,lam,op,law,term

BOOL=value('Bool')
FALSE=term(BOOL,{'Bool':False})
def operation(t):
 n=t['node'];return n.get('Op')if isinstance(n,dict)else None
def apply(f,x):return op(f['sort']['Arrow'][1],'apply',f,x)
def trans(m,a,b):return {'Trans':dict(middle=m,left=a,right=b)}
def use(i,args,**extra):return {'Use':dict(law=i,arguments=args,premises=[],**extra)}

def unfold(t,core,subject):
 functions={f['name']:f for f in core['program']['functions']};remaining=[30000]
 def walk(t,active=()):
  remaining[0]-=1
  if remaining[0]<0 or len(active)>32:raise ValueError('dedup source expansion budget')
  t=map_children(t,lambda c:walk(c,active));node=operation(t)
  if node and node[0].startswith('call:')and node[0][5:]in functions:
   name=node[0][5:]
   if name in active:raise ValueError('recursive helper outside dedup discovery')
   f=functions[name];args={n:a for (n,_),a in zip(f['params'],node[1])}
   return walk(substitute(subject['functions'][name],args),(*active,name))
  return t
 return beta_normalize(walk(t),budget=100000)

def sites(body,word_type):
 """Observe a word list directly or through immutable record projections."""
 words=value({'List':word_type})
 for path,target in positions(body):
  if target['sort']!=words or not closed(target):continue
  fold=target;projection=[]
  while (node:=operation(fold))and node[0].startswith('field:')and len(node[1])==1:
   projection.append(0);fold=node[1][0]
  node=operation(fold)
  if not node or node[0]!='call:foldl' or len(node[1])!=3:continue
  xs,initial,step=node[1]
  if xs['sort']!=words or not closed(fold):continue
  observer=lam(initial['sort'],replace(shift(target,1),tuple(projection),bound(initial['sort'],0)))
  yield path,target,xs,initial,step,observer

def membership_proof(scan,items,key,names,word_type):
 word=value(word_type)
 node=operation(scan)
 if not node or node[0]not in ['call:foldl','call:foldr']or len(node[1])!=3:return None
 xs,seed,step=node[1]
 if xs!=items or seed!=FALSE:return None
 try:body=step['node']['Lambda']['node']['Lambda']
 except(KeyError,TypeError):return None
 # The predicate's key is captured under the two callback parameters.
 equality=op(BOOL,'binary:==',shift(key,2),bound(word,1))
 reversed_equality=op(BOOL,'binary:==',bound(word,1),shift(key,2))
 found=bound(BOOL,0)
 if node[0]=='call:foldl':
  if body==op(BOOL,'binary:||',found,equality):name='membership_left'
  elif body==op(BOOL,'binary:||',found,reversed_equality):name='membership_left_reversed'
  else:return None
  return use(names[name],dict(xs=items,key=key))
 if body==op(BOOL,'binary:||',equality,found):return 'Normalize'
 singleton=lambda x:term(value({'List':word_type}),{'Cons':[x,term(value({'List':word_type}),'Nil')]})
 structural=op(BOOL,'binary:==',singleton(bound(word,1)),singleton(shift(key,2)))
 if body==op(BOOL,'binary:||',structural,found):return use(names['membership_structural'],dict(xs=items,key=key))
 return None

def propose(context,limit=4):
 if limit<=0:return
 used=0
 for word_type in ['U32','U64','I32']:
  for proposal in propose_word(context,word_type,limit-used):
   yield proposal;used+=1
   if used>=limit:return

def propose_word(context,word_type,limit):
 word=value(word_type);words=value({'List':word_type})
 if limit<=0 or context.get('representation'):return
 core=context['core'];functions=core['program']['functions']
 # Cheap discovery filter, never evidence for an equality.
 if not any('foldl' in canonical(f['body']).decode() for f in functions):return
 root=Path(context['knowledge_root']);store=Store(root,root/'store/snapshots'/(context['knowledge_snapshot']+'.json'))
 compiler=context['compiler']
 def invoke(*args):
  r=subprocess.run([compiler,*map(str,args)],capture_output=True,text=True,timeout=context.get('check_timeout',120))
  if r.returncode:raise ValueError(r.stderr[-3000:])
  return json.loads(r.stdout)if r.stdout.lstrip().startswith(('{','['))else r.stdout
 with tempfile.TemporaryDirectory(prefix='ink-indexed-dedup-')as temporary:
  d=Path(temporary);original=d/'original.json';original.write_bytes(canonical(core))
  original_semantic=d/'original-semantic.json';invoke('emit-semantic',original,'--core','-o',original_semantic)
  original_subject=json.loads(original_semantic.read_bytes());rows=[]
  for f in functions:
   try:normalized=unfold(original_subject['functions'][f['name']],core,original_subject)
   except (ValueError,KeyError):continue
   for site in sites(normalized,word_type):
    if not any(t['sort']==BOOL and operation(t)and operation(t)[0]in ['call:foldl','call:foldr']for _,t in positions(site[4])):continue
    rows.append((f,normalized,site))
    if len(rows)>=limit:break
   if len(rows)>=limit:break
  if not rows:return
  prefix='indexed_'+word_type.lower()+'_'+context['source'][:16]+'_'
  symbols=['IndexedWords','empty_words','member','key_index','encode_words','dedup_step','indexed_step']
  occupied={f['name']for f in functions}|set(core['program']['records'])
  while any(prefix+n in occupied for n in symbols):prefix+='x'
  helper={n:prefix+n for n in symbols}
  source,proofs=documents(word_type)
  source=re.sub(r'\b('+'|'.join(symbols)+r')\b',lambda m:helper[m[0]],source)
  (d/'laws.ink').write_text(source);(d/'proofs.json').write_bytes(canonical(proofs))
  authored=invoke('emit-laws',d/'laws.ink','--proofs',d/'proofs.json','-o',d/'laws.json')
  names=authored['names'];objects=json.loads((d/'laws.json').read_bytes())['objects']
  helpers=(Path(__file__).resolve().parents[1]/'libraries/indexed-dedup-u32.ink').read_text().split('law index_membership')[0].replace('u32',word_type.lower())
  helpers=re.sub(r'\b('+'|'.join(symbols)+r')\b',lambda m:helper[m[0]],helpers)
  (d/'helpers.ink').write_text(helpers);invoke('emit-core',d/'helpers.ink','-o',d/'helpers.json')
  p=json.loads((d/'helpers.json').read_bytes())['program']
  extension=entry('definition','ink-source-extension-v1',{k:p[k]for k in ['functions','records','enums','ids']});eid=identity(extension)
  request=dict(schema=1,semantics='ink-source-extension-v1',input_core_sha256=context['source'],extension=eid,knowledge=ProposalViews(store,{eid:extension},d/'extension').bundle([eid]))
  (d/'extension.json').write_bytes(canonical(request));receipt=invoke('extend-core',original,d/'extension.json','--core','-o',d/'extended.json')
  extended=json.loads((d/'extended.json').read_bytes());invoke('emit-semantic',d/'extended.json','--core','-o',d/'semantic.json');subject=json.loads((d/'semantic.json').read_bytes())
  for f,normalized,(path,target,xs,initial,step,observer)in rows:
   label='indexed-ordered-dedup/'+f['name']+'/'+'.'.join(map(str,path))
   try:
    params=free_parameters(original_subject['functions'][f['name']]);scope=set(params);fresh={}
    for name in ['item','state']:
     actual='__assumed_'+name
     while actual in scope:actual+='_'
     scope.add(actual);fresh[name]=actual
    item=var(word,fresh['item']);state=var(initial['sort'],fresh['state'])
    observed=beta_normalize(apply(observer,state));before=unfold(apply(observer,apply(apply(step,item),state)),core,original_subject)
    member=op(BOOL,'call:'+helper['member'],observed,item)
    matches=[]
    for subpath,scan in positions(before):
     if not closed(scan):continue
     proof=membership_proof(scan,observed,item,names,word_type)
     if proof is not None:matches.append((subpath,scan,proof))
    if len(matches)!=1:continue
    subpath,scan,scan_proof=matches[0];changed=replace(before,subpath,member)
    branch={'Cases':dict(condition=member,on_true='Normalize',on_false='Normalize')}
    assumption=trans(before,'Normalize',trans(changed,lift(before,subpath,scan_proof),branch))
    logical_step=lam(word,lam(words,op(words,'call:'+helper['dedup_step'],bound(word,1),bound(words,0))))
    args=dict(xs=xs,physical=initial,observe=observer,logical_step=logical_step,physical_step=step)
    types={'A':word_type,'L':{'List':word_type},'P':initial['sort']['Value']}
    observation=instantiate(objects[names['foldl_observation']]['payload'],types)
    first=substitute(observation['from'],args);middle=substitute(observation['to'],args)
    observation_proof=use(names['foldl_observation'],args,types=types,assumptions=[assumption])
    dedup_args={'xs':xs,'initial':beta_normalize(apply(observer,initial))}
    dedup=objects[names['dedup_indexed_from']]['payload'];logical=substitute(dedup['from'],dedup_args);selected=substitute(dedup['to'],dedup_args)
    proof=trans(first,'Normalize',trans(middle,observation_proof,trans(logical,'Normalize',use(names['dedup_indexed_from'],dedup_args))))
    result=replace(normalized,path,selected)
    theorem=law(params,original_subject['functions'][f['name']],result,trans(normalized,'Normalize',lift(normalized,path,proof)),dependencies=[names[n]for n in ['foldl_observation','dedup_indexed_from','membership_left','membership_left_reversed','membership_structural']])
    theorem['semantics']='ink-general-laws-v1';theorem=bind(theorem,extended,subject)
    obj=semantic_entry(theorem);lid=identity(obj);view=ProposalViews(store,{**objects,lid:obj},d/('proof-'+str(len(path)))).bundle([lid])
    packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=receipt['core_sha256'],knowledge=view,applications=[dict(function=f['name'],path=[],law=lid,arguments={n:var(s,n)for n,s in params.items()},premises=[])])
    yield dict(status='proposal',label=label,steps=[dict(kind='extension',package=request),dict(kind='rewrite',package=packet)])
   except (ValueError,KeyError,TypeError)as error:
    yield dict(status='declined',label=label,reason=str(error))
