import unittest
from ink_knowledge import identity
from producers.numeric_text_laws import objects,SIGNATURES
class PrimitiveChoiceLaws(unittest.TestCase):
 def test_each_fixed_signature_has_independent_argument_laws(self):
  rows=objects();self.assertEqual(len(rows),39);self.assertEqual(len({identity(o)for _,o in rows}),39)
  for _,o in rows:
   law=o['payload'];self.assertEqual(law['conditions'],[]);self.assertEqual(o['dependencies'],[])
   self.assertEqual(set(law['proof']),{'Cases'});self.assertEqual(law['to']['node']['Op'][0],'call:choose')
   self.assertTrue(law['from']['node']['Op'][0].startswith('call:'))
