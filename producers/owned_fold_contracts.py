"""Untrusted transport of generic owned-fold observation laws to source goals.

Only the ordinary kernel decides whether the actual source step satisfies the
observer assumption. This producer contains no privileged storage-family names.
"""
import copy
from ink_knowledge import Store,identity,semantic_entry
from ink_planner.semantic_search import children,positions,substitute,shift,replace
from producers.semantic_laws import value,var,bound,lam,op
from producers.beta_specialization15 import beta_normalize

def instantiate(value_,types):
 if isinstance(value_,dict):
  if set(value_)=={'Named'} and value_['Named'] in types:return copy.deepcopy(types[value_['Named']])
  return {k:instantiate(x,types)for k,x in value_.items()}
 if isinstance(value_,list):return [instantiate(x,types)for x in value_]
 return value_

def closed(t,depth=0):
 n=t['node']
 return not(isinstance(n,dict)and 'Bound'in n and n['Bound']>=depth)and all(closed(c,depth+int(isinstance(n,dict)and 'Lambda'in n))for c in children(t))

def lift(t,path,proof):
 if not path:return proof
 return {'Congruence':[lift(c,path[1:],proof)if i==path[0]else 'Normalize'for i,c in enumerate(children(t))]}

def propose(goal,context,view,names):
 from producers.contract_proofs import context_for,pure_proposals
 def unfold(term,depth=0):
  if depth>64:raise ValueError('owned fold source unfolding depth')
  from ink_planner.semantic_search import map_children
  term=map_children(term,lambda child:unfold(child,depth+1))
  node=term['node'];operator=node.get('Op')if isinstance(node,dict)else None
  if operator and operator[0].startswith('call:'):
   definition=context['definitions'].get(operator[0][5:])
   if definition:
    body=definition['definition'];args={name:arg for (name,_),arg in zip(body['params'],operator[1])}
    return unfold(substitute(body['body'],args),depth+1)
  return term
 normalized=beta_normalize(unfold(goal['goal']['from']),budget=100000)
 observe_id=names['foldl_observe_append'];push_id=names['buffer_push_append']
 observe_law=view['objects'][observe_id]['payload'];push_law=view['objects'][push_id]['payload']
 attempts=0
 for path,target in positions(normalized):
  t=target['sort'].get('Value')if isinstance(target['sort'],dict)else None
  if not isinstance(t,dict)or set(t)!={'List'}or not closed(target):continue
  fold=target;fold_path=[]
  while True:
   node=fold['node'];operation=node.get('Op')if isinstance(node,dict)else None
   if not operation:break
   if operation[0]=='call:foldl':break
   if operation[0]=='method:freeze'or operation[0].startswith('field:'):
    fold_path.append(0);fold=operation[1][0];continue
   break
  node=fold['node'];operation=node.get('Op')if isinstance(node,dict)else None
  if not operation or operation[0]!='call:foldl':continue
  xs,initial,step=operation[1];acc=initial['sort'];item=value(t['List'])
  if xs['sort']!=value({'List':t['List']}):continue
  observer_body=replace(shift(target,1),tuple(fold_path),bound(acc,0));observer=lam(acc,observer_body)
  types={'A':t['List'],'S':acc['Value']};inst=instantiate(observe_law,types)
  args=dict(xs=xs,initial=initial,step=step,observe=observer)
  left=substitute(inst['from'],args);right=substitute(inst['to'],args)
  # Fresh parameters follow the kernel's assumption instantiation discipline.
  scope=set(goal['params']);fresh={}
  for name in ['item','state']:
   actual='__assumed_'+name
   while actual in scope:actual+='_'
   scope.add(actual);fresh[name]=actual
  element=var(item,fresh['item']);state=var(acc,fresh['state']);observed=op(target['sort'],'apply',observer,state)
  push_args=dict(items=observed,item=element);push=instantiate(push_law,{'A':t['List']})
  before=substitute(push['from'],push_args);after=substitute(push['to'],push_args)
  assumption={'Trans':dict(middle=before,left='Normalize',right={'Trans':dict(middle=after,left={'Use':dict(law=push_id,types={'A':t['List']},arguments=push_args,premises=[])},right='Normalize')})}
  use={'Use':dict(law=observe_id,types=types,arguments=args,premises=[],assumptions=[assumption])}
  proof={'Trans':dict(middle=left,left='Normalize',right=use)}
  # A fully empty initial observation can reduce to the input. This remains a
  # proposed conversion; an arbitrary initial owner cannot be discarded.
  proof={'Trans':dict(middle=right,left=proof,right='Normalize')}
  params={n:s for n,s in goal['params'].items()}
  law=dict(schema=1,semantics='ink-general-laws-v1',params=params,conditions=[],**{'from':target,'to':xs},proof=proof,dependencies=[observe_id,push_id])
  law['definition_context']=context_for(context,law)
  obj=semantic_entry(law);ident=identity(obj)
  import tempfile
  with tempfile.TemporaryDirectory(prefix='ink-owned-fold-')as directory:
   bank=Store.publish(directory,[*view['objects'].values(),obj]);bundle=bank.bundle([ident])
  rewritten=replace(normalized,path,xs)
  application={'Use':dict(law=ident,arguments={n:var(s,n)for n,s in params.items()},premises=[])}
  bridge={'Trans':dict(middle=normalized,left='Normalize',right=lift(normalized,path,application))}
  for terminal in pure_proposals({**goal,'goal':{'from':rewritten,'to':goal['goal']['to']}}):
   attempts+=1
   if attempts>32:return
   yield {'Trans':dict(middle=rewritten,left=bridge,right=terminal)},bundle

def proposals(goal,store,context):
 import json
 names=json.loads((store.data/'names.json').read_text())
 selected={name:names['storage-observations/'+name]for name in ('foldl_observe_append','buffer_push_append')}
 yield from propose(goal,context,store.bundle(list(selected.values())),selected)
