"""Move loop-invariant choices outside pure traversals; ordinary kernel proofs.

Developed against separate conditional particle/selection workloads. No float
reassociation, speculative callback execution, target matcher or new primitive.
"""
from ink_knowledge import entry,identity,semantic_entry,Store
from ink_knowledge.law_templates import SEMANTICS,substitute_types
from producers.semantic_laws import value,arrow,var,bound,lam,op,law

def templates():
 a,b,s=[value({'Named':'$'+n}) for n in ('A','B','S')]
 la,lb=value({'List':{'Named':'$A'}}),value({'List':{'Named':'$B'}})
 boolean=value('Bool');xs=var(la,'xs');c=var(boolean,'c');z=var(s,'z')
 choose=lambda q,x,y:op(x['sort'],'call:choose',q,x,y)
 apply=lambda f,x:op(f['sort']['Arrow'][1],'apply',f,x)
 induction={'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step='Normalize')}
 proof={'Cases':dict(condition=c,on_false=induction,on_true=induction)}
 rows=[]
 def add(name,types,params,src,dst):
  rows.append(dict(name=name,object=entry('definition',SEMANTICS,dict(type_parameters=types,law=law(params,src,dst,proof),dependencies={}))))
 f,g=var(arrow(a,b),'f'),var(arrow(a,b),'g')
 mapped=lambda callback:op(lb,'method:map',xs,callback)
 add('map-invariant-choice',['A','B'],dict(xs=la,c=boolean,f=f['sort'],g=g['sort']),mapped(lam(a,choose(c,apply(f,bound(a,0)),apply(g,bound(a,0))))),choose(c,mapped(f),mapped(g)))
 p,q=var(arrow(a,boolean),'p'),var(arrow(a,boolean),'q')
 filtered=lambda callback:op(la,'method:filter',xs,callback)
 add('filter-invariant-choice',['A'],dict(xs=la,c=boolean,p=p['sort'],q=q['sort']),filtered(lam(a,choose(c,apply(p,bound(a,0)),apply(q,bound(a,0))))),choose(c,filtered(p),filtered(q)))
 f,g=var(arrow(a,arrow(s,s)),'f'),var(arrow(a,arrow(s,s)),'g')
 reduce=lambda step,x,acc:apply(apply(step,x),acc)
 callback=lam(a,lam(s,choose(c,reduce(f,bound(a,1),bound(s,0)),reduce(g,bound(a,1),bound(s,0)))))
 folded=lambda step:op(s,'call:foldr',xs,z,step)
 add('foldr-invariant-choice',['A','S'],dict(xs=la,c=boolean,z=s,f=f['sort'],g=g['sort']),folded(callback),choose(c,folded(f),folded(g)))
 return rows

def concrete():
 rows=[]
 for template in templates():
  for t in ['U32','I32','F32','Bool','String',{'List':'U32'}]:
   args={n:t for n in template['object']['payload']['type_parameters']}
   rows.append((template['name']+'/'+str(t),semantic_entry(substitute_types(template['object']['payload']['law'],args))))
 return rows

def publish(root):
 rows=templates();instances=concrete()
 return Store(root).extend([r['object'] for r in rows]+[o for _,o in instances],{**{'invariant-choice/'+r['name']:identity(r['object'])for r in rows},**{'invariant-choice/instance/'+n:identity(o)for n,o in instances}})
