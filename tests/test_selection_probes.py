import unittest
from ink_knowledge.selection_probes import create,supported

class TypedProbes(unittest.TestCase):
    def test_boundary_inputs_are_typed_and_do_not_depend_on_source_name(self):
        program=dict(records={'R':[['x','I32'],['flag','Bool']]},functions=[dict(name='entry',params=[['rows',{'List':{'Named':'R'}}],['key','I32']],result='Bool',body={'Num':17})])
        spec,receipt=create(dict(program=program));calls=spec['phases']['call:entry']
        self.assertEqual(len(calls),24);self.assertEqual(receipt['calls'],24)
        self.assertEqual({len(c['args'][0])for c in calls},{0,8,128,2048})
        for c in calls:
            for r in c['args'][0]:self.assertTrue(-2147483648<=r['x']<=2147483647 and type(r['flag'])is bool)
        program['functions'][0]['name']='unrelated'
        other,_=create(dict(program=program));self.assertEqual([c['args']for c in calls],[c['args']for c in other['phases']['call:unrelated']])
    def test_declines_effectful_recursive_and_inexact_transfer_boundaries(self):
        self.assertIsNone(create(dict(program=dict(states=['state'],functions=[])))[0])
        self.assertFalse(supported({'Named':'Node'},{'Node':[['tail',{'List':{'Named':'Node'}}]]}))
        self.assertFalse(supported('U64',{}))
        self.assertFalse(supported({'Arrow':['U32','U32']},{}))
