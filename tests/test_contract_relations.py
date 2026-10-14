import unittest
from ink_knowledge.store import entry,identity
from producers.contract_proofs import state_proof

class ConstructorRelations(unittest.TestCase):
 def fixture(self):
  obj=entry('definition','first-order-inductive-equality-v1',{'declaration':{'Datatype':{'constructors':[{'name':'None','fields':[]},{'name':'Some','fields':['U64']}]}}})
  key=identity(obj)
  value=lambda x:{'Construct':dict(datatype=key,constructor=1,arguments=[x])}
  return key,{key:obj},value
 def test_a_constructor_payload_equality_reaches_a_scalar_goal(self):
  _,objects,value=self.fixture();x={'Var':'payload'};two={'U64':2}
  proof=state_proof(objects,x,two,{'payload':'U64'},[(value(two),value(x),0)])
  self.assertIn('Substitute',str(proof))
 def test_disjoint_constructor_equality_exposes_a_contradiction(self):
  key,objects,value=self.fixture();none={'Construct':dict(datatype=key,constructor=0,arguments=[])}
  proof=state_proof(objects,{'Bool':False},{'Bool':True},{},[(none,value({'U64':2}),0)])
  self.assertIn('Hypothesis',str(proof))

if __name__=='__main__':unittest.main()
