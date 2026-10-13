import unittest
from ink_knowledge import identity
from producers.invariant_choice_templates import templates,concrete
class InvariantChoice(unittest.TestCase):
 def test_generic_lazy_traversals_are_unconditional_and_not_source_specialisations(self):
  rows=templates();self.assertEqual(len(rows),3);self.assertEqual(len({identity(r['object'])for r in rows}),3)
  self.assertEqual(len(concrete()),18);self.assertEqual(len({identity(o)for _,o in concrete()}),18)
  for row in rows:
   p=row['object']['payload'];self.assertEqual(p['dependencies'],{});self.assertEqual(p['law']['conditions'],[])
   self.assertEqual(set(p['law']['proof']),{'Cases'});self.assertNotIn('definition_context',p['law'])
   self.assertEqual(p['law']['to']['node']['Op'][0],'call:choose')
