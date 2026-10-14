import unittest
from producers.proof_composition import balance_transitivity

class ProofComposition(unittest.TestCase):
 def leaves(self,p):
  if isinstance(p,dict) and set(p)=={'Trans'}:return self.leaves(p['Trans'][0])+self.leaves(p['Trans'][1])
  return [p]
 def height(self,p):
  if isinstance(p,dict) and set(p)=={'Trans'}:return 1+max(map(self.height,p['Trans']))
  return 0
 def test_long_chains_keep_every_leaf_in_order(self):
  proof={'Hypothesis':0}
  for i in range(1,256):proof={'Trans':[proof,{'Hypothesis':i}]}
  balanced=balance_transitivity(proof)
  self.assertEqual(self.leaves(balanced),[{'Hypothesis':i} for i in range(256)])
  self.assertEqual(self.height(balanced),8)
 def test_induction_substitution_and_symmetry_remain_boundaries(self):
  proof={'Trans':[{'Sym':{'Trans':[{'Hypothesis':0},{'Hypothesis':1}]}},{'Induction':dict(variable='xs',**{'from':{'Var':'xs'},'to':{'Var':'xs'}},cases=[dict(bindings=['head','tail'],proof={'Trans':[{'Hypothesis':2},{'Hypothesis':3}]})])}]}
  balanced=balance_transitivity(proof)
  self.assertEqual(self.leaves(balanced),self.leaves(proof))
  with self.assertRaises(ValueError):balance_transitivity({'Trans':['Normalize']})

if __name__=='__main__':unittest.main()
