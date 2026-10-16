import copy
import random
import unittest
from ink_knowledge import canonical
from producers.conditional_cover import boolean_cover
from producers.rup_transport import encode_hints, decode_hints, pack_certificate, unpack_certificate
from producers.rup_compaction import compact_certificate


class HintTransport(unittest.TestCase):
    def test_exact_boundaries_signed_deltas_and_immutable_certificate(self):
        words = [0, 1, 31, 32, 1023, 1024, 32767, 32768, 319999, 0]
        self.assertEqual(encode_hints(words), 'AC8BC-9BC-_9BC-_wR9_wT')
        rng = random.Random(217)
        for indices in [words, [0] * 100000, [rng.randrange(320000) for _ in range(10000)]]:
            self.assertEqual(decode_hints(encode_hints(indices)), indices)
        proof = dict(encoding='shared-v2', problem_sha256='bound', note='preserved', steps=[
            dict(clause=[3], hints=list(range(10000, 10300))),
            dict(clause=[], hints=[0, 1]),
        ])
        before = copy.deepcopy(proof)
        packed = pack_certificate(proof)
        self.assertEqual(unpack_certificate(packed), proof)
        self.assertEqual(proof, before)
        self.assertLess(len(canonical(packed)), len(canonical(proof)))
        self.assertEqual(pack_certificate(packed), packed)
        self.assertEqual(packed['steps'][0]['hints'], [])
        self.assertEqual(packed['problem_sha256'], 'bound')

    def test_resource_canonical_and_ambiguous_inputs_decline(self):
        for indices in [[], [True], [-1], [320000], [0] * 100001]:
            with self.assertRaises(ValueError): encode_hints(indices)
        for text in ['', 'g', 'gA', 'ggggA', 'B', 'ggxT', '_____', 'é', ' ', '=', 'A'*100001, 'A'*400001]:
            with self.assertRaises(ValueError): decode_hints(text)
        with self.assertRaisesRegex(ValueError, 'both'):
            unpack_certificate(dict(steps=[dict(clause=[], hints=[0], hint_deltas_v1='A')]))

    def test_compaction_understands_packed_input_without_treating_it_as_no_hints(self):
        problem = dict(sha256='bound', clauses=[[1], [-1]])
        proof = dict(problem_sha256='bound', steps=[dict(clause=[], hints=[], hint_deltas_v1='AC')])
        before = copy.deepcopy(proof)
        result, _ = compact_certificate(problem, proof)
        self.assertEqual(unpack_certificate(result)['steps'][-1]['clause'], [])
        self.assertEqual(proof, before)
        with self.assertRaises(ValueError):
            compact_certificate(problem, dict(proof, steps=[dict(clause=[], hints=[], hint_deltas_v1='=')]))


class BooleanCover(unittest.TestCase):
    def leaf(self, conditions, selected=None):
        boolean = {'Value':'Bool'}
        premises = [dict(**{'from':dict(node={'Free':name},sort=boolean),
                           'to':dict(node={'Bool':value},sort=boolean)}) for name,value in conditions]
        return dict(schema=1,semantics='test',params={'a':boolean,'b':boolean},dependencies=[],conditions=premises,
            **{'from':dict(node={'Word':1},sort={'Value':'U64'}), 'to':dict(node={'Word':1},sort={'Value':'U64'})},
            proof={'BitVector':dict(hypotheses=list(range(len(premises))) if selected is None else selected,
                certificate=dict(problem_sha256='replay-required',steps=[dict(clause=[],hints=[0,1])]))})

    def test_complete_cover_preserves_context_and_reorders_only_selected_premises(self):
        # The second witness lists b before a, while the case tree reaches a
        # first. Extra path premises must not enter or reorder its CNF.
        cells = [self.leaf([('a',True)]), self.leaf([('b',True),('a',False)]), self.leaf([('b',False)])]
        before = copy.deepcopy(cells)
        result = boolean_cover(cells)
        self.assertEqual(result['conditions'], [])
        branch = result['proof']['Cases']['on_false']['Cases']['on_true']['BitVector']
        self.assertEqual(branch['hypotheses'], [1,0])
        self.assertEqual(branch['certificate'], cells[1]['proof']['BitVector']['certificate'])
        self.assertEqual(cells,before)
        self.assertEqual(result['from'],cells[0]['from'])
        self.assertEqual(result['to'],cells[0]['to'])

    def test_incomplete_mismatched_and_exhausted_covers_never_publish_a_root(self):
        with self.assertRaisesRegex(ValueError,'do not cover'):
            boolean_cover([self.leaf([('a',True)])])
        left,right=self.leaf([('a',False)]),self.leaf([('a',True)])
        bad=copy.deepcopy(right);bad['to']['node']['Word']=2
        with self.assertRaisesRegex(ValueError,'matching statements'):
            boolean_cover([left,bad])
        with self.assertRaisesRegex(ValueError,'leaf limit'):
            boolean_cover([left,right],maximum_leaves=1)
        with self.assertRaisesRegex(ValueError,'premise indices'):
            boolean_cover([self.leaf([('a',True)],[1])])
        with self.assertRaisesRegex(ValueError,'depth limit'):
            boolean_cover([self.leaf([('a',True),('b',True)]),self.leaf([('a',False)]),self.leaf([('b',False)])],maximum_depth=1)


if __name__ == '__main__':
    unittest.main()
