"""Untrusted flat postorder transport of existing typed semantic term trees."""
import copy
def depth(value):
 pending=[(value,0)];maximum=0
 while pending:
  value,d=pending.pop();maximum=max(maximum,d)
  if isinstance(value,dict):pending.extend((x,d+1)for x in value.values())
  elif isinstance(value,list):pending.extend((x,d+1)for x in value)
 return maximum
def children(term):
 node=term['node']
 if isinstance(node,dict):
  if 'Lambda'in node:return [node['Lambda']]
  if 'Cons'in node:return node['Cons']
  if 'Op'in node:return node['Op'][1]
 return []
def encode(term):
 pending=[(term,False,0)];nodes=[];roots=[]
 while pending:
  value,exit,d=pending.pop()
  if d>128:raise ValueError('flat term depth limit')
  args=children(value)
  if not exit:
   pending.append((value,True,d));pending.extend((x,False,d+1)for x in reversed(args));continue
  if len(nodes)>=100000:raise ValueError('flat term node limit')
  count=len(args);indices=roots[-count:]if count else []
  if count:del roots[-count:]
  node=value['node']
  if isinstance(node,dict)and 'Lambda'in node:node={'Lambda':indices[0]}
  elif isinstance(node,dict)and 'Cons'in node:node={'Cons':indices}
  elif isinstance(node,dict)and 'Op'in node:node={'Op':[node['Op'][0],indices]}
  else:node=copy.deepcopy(node)
  roots.append(len(nodes));nodes.append(dict(sort=copy.deepcopy(value['sort']),node=node))
 if len(roots)!=1:raise ValueError('flat term root')
 return dict(schema=1,root=roots[0],nodes=nodes)
def body(term):return encode(term)if depth(term)>80 else term
