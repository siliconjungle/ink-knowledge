import unittest
from ink_knowledge.selection_probes import create,supported,stratify

class TypedProbes(unittest.TestCase):
    def test_boundary_inputs_are_typed_and_do_not_depend_on_source_name(self):
        program=dict(records={'R':[['x','I32'],['flag','Bool']]},functions=[dict(name='entry',params=[['rows',{'List':{'Named':'R'}}],['key','I32']],result='Bool',body={'Num':17})])
        spec,receipt=create(dict(program=program));calls=[c for rows in spec['phases'].values() for c in rows]
        self.assertEqual(len(calls),24);self.assertEqual(receipt['calls'],24)
        self.assertEqual({len(c['args'][0])for c in calls},{0,8,128,2048})
        for c in calls:
            for r in c['args'][0]:self.assertTrue(-2147483648<=r['x']<=2147483647 and type(r['flag'])is bool)
        program['functions'][0]['name']='unrelated'
        self.assertEqual(sum(spec['profile'].values()),10000)
        self.assertEqual(len(spec['phases']),4)
        for rows in spec['phases'].values():self.assertEqual(len({len(c['args'][0])for c in rows}),1)
        other,_=create(dict(program=program));self.assertEqual([c['args']for c in calls],[c['args']for rows in other['phases'].values()for c in rows])
    def test_declines_effectful_recursive_and_inexact_transfer_boundaries(self):
        self.assertIsNone(create(dict(program=dict(states=['state'],functions=[])))[0])
        self.assertFalse(supported({'Named':'Node'},{'Node':[['tail',{'List':{'Named':'Node'}}]]}))
        self.assertFalse(supported('U64',{}))
        self.assertFalse(supported({'Arrow':['U32','U32']},{}))

    def test_checked_wire_profiles_cover_finite_recursive_sums_and_exact_words(self):
        node={'Named':'Node'}
        records={'Node':[['value','U64'],['next',{'Option':node}]]}
        program=dict(records=records,functions=[dict(name='entry',params=[['node',node],['pair',{'Vector':['F32',2]}],['choice',{'Result':['Unit','String']}]],result=node,body={})])
        spec,receipt=create(dict(program=program),'javascript')
        self.assertEqual(receipt['declined'],[])
        self.assertEqual(set(spec['phases']),{'call:entry:portable','call:entry:compact'})
        self.assertEqual(spec['schema'],3)
        for calls in spec['phases'].values():
            for call in calls:
                node,pair,choice=call['args'];depth=0
                while True:
                    self.assertIsInstance(node['value'],int)
                    self.assertLessEqual(int(node['value']),2**64-1)
                    depth+=1;self.assertLess(depth,16)
                    if 'None'in node['next']:break
                    node=node['next']['Some']
                self.assertEqual(len(pair),2)
                self.assertTrue(all(type(v)is float for v in pair))
                self.assertTrue(set(choice)in ({'Ok'},{'Err'}))
        self.assertIsNone(create(dict(program=program),'rust')[0])

    def test_uninhabited_and_unsupported_recursive_signatures_decline(self):
        for records in [{'Loop':[['next',{'Named':'Loop'}]]},{'Loop':[['next',{'Result':[{'Named':'Loop'},{'Named':'Loop'}]}]]},{'Loop':[['next',{'Option':{'Arrow':['U32','U32']}}]]}]:
            program=dict(records=records,functions=[dict(name='entry',params=[['x',{'Named':'Loop'}]],result='Bool',body={})])
            self.assertIsNone(create(dict(program=program),'javascript')[0])

    def test_recursive_result_selects_a_finite_branch_at_depth_bound(self):
        loop={'Named':'Loop'}
        records={'Loop':[['tail',{'Result':[loop,{'Vector':['U32',4]}]}]]}
        program=dict(records=records,functions=[dict(name='entry',params=[['x',loop]],result='Bool',body={})])
        spec,_=create(dict(program=program),'javascript')
        self.assertTrue(spec['phases'])
        for calls in spec['phases'].values():
            for call in calls:
                v=call['args'][0];depth=0
                while 'Ok'in v['tail']:
                    v=v['tail']['Ok'];depth+=1;self.assertLess(depth,16)
                self.assertEqual(len(v['tail']['Err']),4)

    def test_first_nested_sequence_uses_profile_sizes_without_recursive_explosion(self):
        records={'Box':[['rows',{'List':{'List':'U32'}}]]}
        program=dict(records=records,functions=[dict(name='entry',params=[['x',{'Named':'Box'}]],result='Bool',body={})])
        spec,_=create(dict(program=program),'javascript')
        calls=[c for phase,rows in spec['phases'].items()if ':compact:' in phase for c in rows]
        sizes={len(c['args'][0]['rows'])for c in calls}
        self.assertEqual(sizes,{0,8,128,2048})
        self.assertTrue(all(len(v)<=1 for c in calls for v in c['args'][0]['rows']))

    def test_phase_budget_retains_calls_weights_and_reports_merged_sizes(self):
        phases={'a':list(range(8)), 'b':list(range(8))}
        sizes={k:[0,0,8,8,128,128,2048,2048]for k in phases}
        divided,weights,receipt=stratify(phases,sizes,10000,5)
        self.assertEqual(len(divided),5)
        for phase in phases:
            keys=[k for k,v in receipt.items()if v['original_phase']==phase]
            self.assertEqual([c for k in keys for c in divided[k]],phases[phase])
            self.assertEqual(sum(weights[k]for k in keys),10000)
        self.assertTrue(any(v['merged_sizes']for v in receipt.values()))
        with self.assertRaisesRegex(ValueError,'phase budget'):stratify(phases,sizes,10000,1)

    def test_integer_weight_rounding_does_not_invent_extra_calls(self):
        divided,weights,receipt=stratify({'x':[0,1,2]}, {'x':[0,8,128]}, 10, 64)
        self.assertEqual(list(weights.values()),[4,3,3])
        self.assertEqual(sum(weights.values()),10)
        self.assertTrue(all(v['ideal_weight_numerator']==10 and v['ideal_weight_denominator']==3 for v in receipt.values()))
        divided,weights,receipt=stratify({'x':[0,1,2,3,4]}, {'x':[0,8,128,2048,4096]}, 2, 64)
        self.assertEqual(sum(weights.values()),2)
        self.assertEqual([v for rows in divided.values()for v in rows],list(range(5)))
        self.assertTrue(all(w>0 for w in weights.values()))

    def test_named_enums_and_identifiers_use_exact_declared_wire_carriers(self):
        program=dict(enums={'Choice':['First','Last']},ids=['Tag'],functions=[dict(name='entry',params=[['tag',{'Named':'Tag'}],['choice',{'Named':'Choice'}]],result={'Named':'Choice'},body={})])
        spec,receipt=create(dict(program=program),'javascript')
        self.assertFalse(receipt['declined'])
        for calls in spec['phases'].values():
            for c in calls:
                tag,choice=c['args'];self.assertRegex(tag,r'^[0-9a-f]{32}$');self.assertIn(choice,{'Choice.First','Choice.Last'})
