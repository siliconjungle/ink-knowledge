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
        sizes={len(c['args'][0]['rows'])for c in spec['phases']['call:entry:compact']}
        self.assertEqual(sizes,{0,8,128,2048})
        self.assertTrue(all(len(v)<=1 for c in spec['phases']['call:entry:compact']for v in c['args'][0]['rows']))

    def test_named_enums_and_identifiers_use_exact_declared_wire_carriers(self):
        program=dict(enums={'Choice':['First','Last']},ids=['Tag'],functions=[dict(name='entry',params=[['tag',{'Named':'Tag'}],['choice',{'Named':'Choice'}]],result={'Named':'Choice'},body={})])
        spec,receipt=create(dict(program=program),'javascript')
        self.assertFalse(receipt['declined'])
        for calls in spec['phases'].values():
            for c in calls:
                tag,choice=c['args'];self.assertRegex(tag,r'^[0-9a-f]{32}$');self.assertIn(choice,{'Choice.First','Choice.Last'})

    def test_contract_roles_not_names_define_probe_entries_and_small_seeds(self):
        import copy
        fn=lambda n:dict(name=n,params=[['xs',{'List':'U32'}],['n','U32']],result='U32',body={'Num':1})
        program=dict(functions=[fn(n)for n in ['entry','body','check','__ink_requires_user']],contracts=dict(implementations=[dict(name='body',specification='entry')],precondition_checks={'entry':'check','body':'check'}))
        spec,receipt=create(dict(program=program),'javascript')
        self.assertEqual(set(spec['phases']),{'call:'+name+':'+mode for name in ['entry','__ink_requires_user']for mode in ['trusted','portable','compact']})
        calls=spec['phases']['call:entry:trusted'];self.assertEqual(len(calls[0]['args'][0]),1);self.assertEqual(calls[0]['args'][1],1)
        self.assertEqual({d['function']for d in receipt['declined']},{'body','check'})
        renamed=copy.deepcopy(program)
        for f in renamed['functions']:f['name']='z'+f['name']
        renamed['contracts']=dict(implementations=[dict(name='zbody',specification='zentry')],precondition_checks={'zentry':'zcheck','zbody':'zcheck'})
        other,_=create(dict(program=renamed),'javascript');self.assertEqual([c['args']for c in calls],[c['args']for c in other['phases']['call:zentry:trusted']])
    def test_policy_rejects_unbounded_or_malformed_seed_cases(self):
        from unittest.mock import patch
        from ink_knowledge import selection_probes as probes
        import json
        policy=probes.policy()
        class Resource:
            def joinpath(self,*args):return self
            def read_text(self):return json.dumps(policy)
        for bad in [[[True,'random']],[[4097,'random']],[[1,[]]],[[1,'unknown']],[[1,'random']]*17]:
            policy['seed_cases']=bad
            with patch.object(probes,'files',return_value=Resource()):
                with self.assertRaisesRegex(ValueError,'seed cases'):probes.policy()
