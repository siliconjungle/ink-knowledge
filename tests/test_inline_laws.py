"""Argument binding must preserve scopes even below callbacks and list cells."""
import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from producers.inline_laws import shared_arguments
from producers.semantic_laws import value,var,op,lam,bound,term

# Small independent evaluator for the proof producer's binder regression cases.
def evaluate(t,free,bindings=()):
 n=t['node']
 if n=='Nil':return []
 if 'Free'in n:return free[n['Free']]
 if 'Bound'in n:return bindings[-n['Bound']-1]
 if 'Word'in n:return n['Word']
 if 'Lambda'in n:return lambda x:evaluate(n['Lambda'],free,(*bindings,x))
 if 'Cons'in n:return [evaluate(n['Cons'][0],free,bindings),*evaluate(n['Cons'][1],free,bindings)]
 name,args=n['Op'];args=[evaluate(a,free,bindings)for a in args]
 if name=='apply':return args[0](args[1])
 if name=='binary:+':return (args[0]+args[1])&0xffffffff
 raise ValueError(name)

class SharedArguments(unittest.TestCase):
 def test_nested_binders_list_cells_and_parameter_order(self):
  u=value('U32');ls=value({'List':'U32'});x=var(u,'x');y=var(u,'y')
  # x,y are formals; two callbacks bind different values at depths 0 and 1.
  item=op(u,'binary:+',op(u,'binary:+',x,bound(u,1)),op(u,'binary:+',y,bound(u,0)))
  literal=term(ls,{'Cons':[item,term(ls,{'Cons':[x,term(ls,'Nil')]})]})
  body=op(ls,'apply',op(lam(u,lam(u,literal))['sort']['Arrow'][1],'apply',lam(u,lam(u,literal)),y),x)
  target=shared_arguments(body,[('x',u),('y',u)])
  for a in [0,1,0xffffffff,0x80000000]:
   for b in [0,3,0xfffffffe]:
    env={'x':a,'y':b}
    self.assertEqual(evaluate(body,env),evaluate(target,env))
    self.assertEqual(evaluate(target,env),[(2*a+2*b)&0xffffffff,a])
 def test_unrelated_free_values_remain_free_and_input_is_not_modified(self):
  import copy
  u=value('U32');body=op(u,'binary:+',var(u,'x'),var(u,'external'));original=copy.deepcopy(body)
  target=shared_arguments(body,[('x',u)])
  self.assertEqual(evaluate(target,{'x':9,'external':4}),13)
  self.assertEqual(body,original)
 def test_subset_sharing_preserves_unbound_formals_under_callbacks(self):
  u=value('U32');x=var(u,'x');y=var(u,'y');z=var(u,'z')
  body=lam(u,op(u,'binary:+',op(u,'binary:+',x,y),op(u,'binary:+',z,bound(u,0))))
  for parameters in [[('x',u)],[('y',u)],[('x',u),('z',u)],[('z',u),('x',u)]]:
   target=shared_arguments(body,parameters)
   for a in [0,1,0xffffffff]:
    env={'x':a,'y':17,'z':3}
    self.assertEqual(evaluate(body,env)(9),evaluate(target,env)(9))

if __name__=='__main__':unittest.main()
