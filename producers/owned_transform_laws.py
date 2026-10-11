"""Universal choices of explicit owned-buffer implementations. No backend matchers."""
from producers.semantic_laws import value,arrow,var,op,law

def named_laws():
 rows=[]
 for t in ('U32','U64','I32','F32','Bool','String','Int','Unit'):
  s=value(t);ls=value({'List':t});bs=value({'Buffer':t});xs=var(ls,'xs')
  for kind in ('map','map_indexed','scan','filter'):
   if kind=='scan'and t not in ('U32','U64','I32','F32'):continue
   ps=arrow(s,value('Bool'))if kind=='filter'else arrow(s,s)if kind=='map'else arrow(value('U32'),arrow(s,s));f=var(ps,'f');args=[]if kind=='scan'else[f]
   source=op(ls,'method:'+kind,xs,*args)
   target=op(ls,'method:freeze',op(bs,'method:'+kind,op(bs,'call:buffer',xs),*args))
   params=dict(xs=ls)
   if kind!='scan':params['f']=ps
   rows.append((f'owned_{kind}_{t.lower()}',law(params,source,target)))
 return rows


def specialize(subject,core=None):
 """Produce ordinary normalization proofs for any admitted element carrier."""
 from ink_planner.semantic_search import positions,children
 from producers.semantic_laws import law,op,value
 rows=[]
 def closed(t,depth=0):
  n=t['node']
  return not(isinstance(n,dict)and 'Bound'in n and n['Bound']>=depth)and all(closed(c,depth+int('Lambda'in n))for c in children(t))
 def free(t,params):
  n=t['node']
  if isinstance(n,dict)and 'Free'in n:params[n['Free']]=t['sort']
  for c in children(t):free(c,params)
 for name,root in sorted(subject['functions'].items()):
  for path,source in positions(root):
   n=source['node'];operator=n.get('Op')if isinstance(n,dict)else None
   if not operator or operator[0]not in ('method:map','method:map_indexed','method:scan','method:filter'):continue
   xs,*args=operator[1];carrier=xs['sort'].get('Value')if isinstance(xs['sort'],dict)else None
   if not isinstance(carrier,dict)or 'List'not in carrier or source['sort']!=xs['sort']or not closed(source):continue
   bs=value({'Buffer':carrier['List']});params={};free(source,params)
   target=op(source['sort'],'method:freeze',op(bs,operator[0],op(bs,'call:buffer',xs),*args))
   rows.append((name+'_owned_'+'_'.join(map(str,path)),law(params,source,target)))
   if len(rows)>=256:return rows
 return rows
