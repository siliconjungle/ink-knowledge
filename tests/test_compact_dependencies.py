import unittest
from producers.compact_observation import declaration_dependencies


class CompactDependencies(unittest.TestCase):
 def test_includes_called_signatures_without_unrelated_carriers(self):
  function, argument, result, unrelated = [c*64 for c in 'abcd']
  objects={function:{'payload':{'declaration':{'Function':{'params':[['x',{'Data':argument}]],'result':{'Data':result}}}}},unrelated:{'payload':{'declaration':{'Datatype':{'constructors':[]}}}}}
  declaration={'Function':{'params':[],'result':'Bool','body':{'Call':{'function':function,'arguments':[]}}}}
  self.assertEqual(declaration_dependencies(declaration,objects),{function,argument,result})
 def test_direct_field_and_proof_references_are_retained(self):
  carrier, theorem = 'a'*64,'b'*64
  declaration={'Theorem':{'params':[['x',{'Data':carrier}]],'proof':{'Use':{'theorem':theorem,'arguments':[]}}}}
  self.assertEqual(declaration_dependencies(declaration,{}),{carrier,theorem})


if __name__=='__main__':unittest.main()
