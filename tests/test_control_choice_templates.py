import unittest
from producers.control_choice_templates import templates,concrete
from ink_knowledge import identity
class ControlChoices(unittest.TestCase):
    def test_templates_preserve_lazy_value_order_without_source_or_target_tags(self):
        rows=templates();self.assertEqual(len(rows),4)
        self.assertEqual(len({identity(r['object']) for r in rows}),4)
        for row in rows:
            p=row['object']['payload'];self.assertEqual(p['type_parameters'],['A'])
            self.assertEqual(p['dependencies'],{});self.assertEqual(p['law']['conditions'],[])
            self.assertEqual(set(p['law']['proof']),{'Cases'})
            self.assertNotIn('definition_context',p['law'])
        self.assertEqual(len(concrete()),24)
        self.assertEqual(len({identity(o) for _,o in concrete()}),24)
