"""Argument binding must preserve scopes even below callbacks and list cells."""
import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from producers.inline_laws import shared_arguments,specialize
from producers.semantic_laws import value,var,op,lam,bound,term

# Small independent evaluator for the proof producer's binder regression cases.
def evaluate(t,free,bindings=()):
 n=t['node']
 if n=='Nil':return []
 if 'Free'in n:return free[n['Free']]
 if 'Bound'in n:return bindings[-n['Bound']-1]
 if 'Word'in n:return n['Word']
 if 'Bool'in n:return n['Bool']
 if 'Lambda'in n:return lambda x:evaluate(n['Lambda'],free,(*bindings,x))
 if 'Cons'in n:return [evaluate(n['Cons'][0],free,bindings),*evaluate(n['Cons'][1],free,bindings)]
 name,args=n['Op']
 if name=='call:choose':return evaluate(args[1]if evaluate(args[0],free,bindings)else args[2],free,bindings)
 if name.startswith('observe:'):
  label=name[8:];free['trace'].append(label);return free['inputs'][label]
 args=[evaluate(a,free,bindings)for a in args]
 if name=='apply':return args[0](args[1])
 if name=='binary:+':
  width={'U32':32,'U64':64}[t['sort']['Value']]
  return (args[0]+args[1])&((1<<width)-1)
 if name=='call:f':
  parameters,body=free['functions']['f'];return evaluate(body,dict(free,**dict(zip(parameters,args))))
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

class StrictUnfolding(unittest.TestCase):
 def test_every_argument_executes_once_in_order_before_a_lazy_body(self):
  from ink_planner.semantic_search import substitute
  u,ls,b,f=value('U64'),value({'List':'U32'}),value('Bool'),value('F32')
  params=[('x','U64'),('ignored',{'List':'U32'}),('gate','Bool'),('tail','U64'),('floating','F32')]
  body=op(u,'call:choose',var(b,'gate'),op(u,'binary:+',var(u,'tail'),op(u,'binary:+',var(u,'x'),var(u,'x'))),term(u,{'Word':0}))
  core={'program':{'functions':[dict(name='f',params=params,result='U64')]}}
  rows=specialize({'functions':{'f':body}},core);self.assertEqual([n for n,_ in rows],['unfold_f'])
  law=rows[0][1]
  # Synthetic observations make strict argument order independently observable,
  # including unused composite/F32 arguments and repeated full-width words.
  arguments={n:op(value(t),'observe:'+n)for n,t in params}
  for gate in [False,True]:
   inputs=dict(x=(1<<63)+13,ignored=[0,7],gate=gate,tail=(1<<64)-1,floating=0x7f800001)
   outcomes=[];traces=[]
   for side in ['from','to']:
    trace=[];env=dict(inputs=inputs,trace=trace,functions={'f':([n for n,_ in params],body)})
    outcomes.append(evaluate(substitute(law[side],arguments),env));traces.append(trace)
   self.assertEqual(outcomes,[25 if gate else 0]*2)
   self.assertEqual(traces,[[n for n,_ in params]]*2)

 def test_nullary_unfolding_has_no_invented_evaluation(self):
  u=value('U64');body=term(u,{'Word':9})
  rows=specialize({'functions':{'constant':body}},{'program':{'functions':[dict(name='constant',params=[],result='U64')]}})
  self.assertEqual(len(rows),1);self.assertEqual(rows[0][1]['to'],body)

if __name__=='__main__':unittest.main()
