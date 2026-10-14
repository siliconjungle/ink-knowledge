"""Untrusted Miller-pattern abstraction for semantic law templates.

Only a free function applied to distinct local variables is abstracted. Other
local dependencies are rejected. Exact adapter endpoints still require normal
kernel proofs; this module grants no rewrite authority.
"""
import copy

def adapter(law_id,law,target):
 """Bridge an exact source site to a higher-order instance by ordinary proof.

 The caller supplies the portable definition context and replays the complete
 closure. Open lexical sites and undischarged premises are never erased.
 """
 from ink_planner.semantic_search import substitute,children
 if law.get('conditions') or law.get('assumptions'):return None
 arguments={}
 if not match(law['from'],target,law['params'],[],{},arguments):
  from .head_beta import reduce
  try:normal=reduce(target)
  except (ValueError,RecursionError):return None
  arguments={}
  if normal is target or not match(law['from'],normal,law['params'],[],{},arguments):return None
 if set(arguments)!=set(law['params']):return None
 params={}
 def free(term,depth=0):
  node=term['node']
  if isinstance(node,dict):
   if 'Bound'in node and node['Bound']>=depth:raise ValueError('open adapter site')
   if 'Free'in node:
    name=node['Free']
    if name in params and params[name]!=term['sort']:raise ValueError('adapter free sort conflict')
    params[name]=term['sort']
  for child in children(term):free(child,depth+int(isinstance(node,dict)and 'Lambda'in node))
 try:
  free(target)
  for argument in arguments.values():free(argument)
 except ValueError:return None
 middle=substitute(law['from'],arguments)
 return dict(semantics='ink-conditional-laws-v1',params=params,conditions=[],
  **{'from':target,'to':substitute(law['to'],arguments)},
  proof={'Trans':dict(middle=middle,left='Normalize',right={'Use':dict(law=law_id,arguments=arguments,premises=[])})},
  dependencies=[law_id])

def applied_hole(pattern,params):
 args=[];head=pattern
 while isinstance(head['node'],dict)and head['node'].get('Op',[None])[0]=='apply':
  items=head['node']['Op'][1]
  if len(items)!=2:return None
  head,arg=items;args.insert(0,arg)
 n=head['node']
 if not args or not isinstance(n,dict)or n.get('Free')not in params:return None
 indices=[]
 for arg in args:
  node=arg['node']
  if not isinstance(node,dict)or set(node)!={'Bound'}:return None
  if type(node['Bound'])is not int or node['Bound']<0:return None
  indices.append(node['Bound'])
 if len(set(indices))!=len(indices):return None
 return head['node']['Free'],args,indices

def abstract(actual,arguments,indices,depth):
 from ink_planner.semantic_search import map_children
 def walk(t,local=0):
  node=t['node']
  if isinstance(node,dict)and 'Bound'in node:
   outer=node['Bound']-local
   if outer<0:return copy.deepcopy(t)
   if outer not in indices or outer>=depth:raise ValueError('unabstracted local dependency')
   return dict(sort=copy.deepcopy(t['sort']),node={'Bound':local+len(indices)-1-indices.index(outer)})
  return map_children(t,lambda child:walk(child,local+int(isinstance(node,dict)and 'Lambda'in node)))
 result=walk(actual)
 for arg in reversed(arguments):result=dict(sort={'Arrow':[copy.deepcopy(arg['sort']),result['sort']]},node={'Lambda':result})
 return result

def match(pattern,actual,params,names,types,arguments,scope=()):
 from .law_templates import unify_type
 from ink_planner.semantic_search import children,extract_hole
 if not unify_type(pattern['sort'],actual['sort'],names,types):return False
 hole=applied_hole(pattern,params)
 if hole:
  name,args,indices=hole
  if any(i>=len(scope)for i in indices):return False
  concrete=[]
  for arg,i in zip(args,indices):
   sort=scope[-1-i]
   if not unify_type(arg['sort'],sort,names,types):return False
   concrete.append(dict(sort=sort,node=arg['node']))
  try:binding=abstract(actual,concrete,indices,len(scope))
  except ValueError:return False
  if not unify_type(params[name],binding['sort'],names,types):return False
  if name in arguments:return arguments[name]==binding
  arguments[name]=binding;return True
 p,a=pattern['node'],actual['node']
 if isinstance(p,dict)and p.get('Free')in params:
  try:binding=extract_hole(actual,len(scope))
  except ValueError:return False
  name=p['Free']
  if name in arguments:return arguments[name]==binding
  arguments[name]=binding;return True
 if type(p)!=type(a):return False
 if not isinstance(p,dict):return p==a
 if set(p)!=set(a):return False
 if 'Op'in p and p['Op'][0]!=a['Op'][0]:return False
 pc,ac=children(pattern),children(actual)
 if not pc:return p==a
 if len(pc)!=len(ac):return False
 nested=scope+(actual['sort']['Arrow'][0],)if 'Lambda'in p else scope
 return all(match(x,y,params,names,types,arguments,nested)for x,y in zip(pc,ac))
