import copy
import importlib.util
import unittest
from unittest.mock import patch

from producers.bitvector_proofs import certificate
from producers.rup_compaction import compact_certificate


def replay(problem, proof):
    """Independent strict sequential RUP interpreter, without watched literals."""
    clauses = copy.deepcopy(problem['clauses'])
    for step in proof['steps']:
        values = {}
        for lit in step['clause']:
            if abs(lit) in values and values[abs(lit)] != (lit < 0):
                break
            values[abs(lit)] = lit < 0
        else:
            conflict = False
            for hint in step['hints']:
                assert not conflict
                source = clauses[hint]
                assert not any(abs(lit) in values and values[abs(lit)] == (lit > 0) for lit in source)
                unknown = [lit for lit in source if abs(lit) not in values]
                assert len(unknown) <= 1
                if not unknown:
                    conflict = True
                else:
                    values[abs(unknown[0])] = unknown[0] > 0
            assert conflict
        clauses.append(step['clause'])
    assert not clauses[-1]


class RupCompactionTests(unittest.TestCase):
    def test_root_conflicts_and_single_use_chains(self):
        # Contradiction is hidden behind a chain; arbitrary variable identities
        # and redundant solver steps must not affect propagation or remapping.
        for start in [1, 7, 100]:
            clauses = [[start], [-start, start + 1], [-start - 1, start + 2], [-start - 2]]
            problem = dict(sha256='synthetic', clauses=clauses, encoding='shared-v2')
            proof = dict(problem_sha256='synthetic', encoding='shared-v2', note='preserved', steps=[
                dict(clause=[start + 1], hints=[0, 1]),
                dict(clause=[start + 2], hints=[4, 2]),
                dict(clause=[], hints=[5, 3]),
            ])
            before = copy.deepcopy((problem, proof))
            result, stats = compact_certificate(problem, proof)
            replay(problem, result)
            self.assertEqual((problem, proof), before)
            self.assertEqual(result['note'], 'preserved')
            self.assertLessEqual(min(stats['candidate_bytes']), stats['candidate_bytes'][0])

    @unittest.skipUnless(importlib.util.find_spec('pysat'), 'optional SAT authoring dependency')
    def test_solver_proofs_with_branching_and_root_facts(self):
        # The four-clause contradiction needs a learned clause: root propagation
        # alone cannot solve it. Independent replay tests both packing stages.
        for depth in [0, 1, 8, 32]:
            gate = depth + 3
            clauses = [[3]] + [[-i, i + 1] for i in range(3, gate)]
            clauses += [[-gate, a, b] for a, b in [(1, 2), (1, -2), (-1, 2), (-1, -2)]]
            problem = dict(sha256='synthetic', clauses=clauses)
            proof = certificate(problem, seconds=5, total_seconds=10)
            before = copy.deepcopy((problem, proof))
            result, stats = compact_certificate(problem, proof)
            replay(problem, proof)
            replay(problem, result)
            self.assertEqual((problem, proof), before)
            self.assertLessEqual(min(stats['candidate_bytes']), stats['candidate_bytes'][0])
            self.assertEqual(result['problem_sha256'], problem['sha256'])

    def test_mismatches_forward_references_and_budget_reject(self):
        problem = dict(sha256='a', clauses=[[1], [-1]])
        proof = dict(problem_sha256='a', steps=[dict(clause=[], hints=[0, 1])])
        for bad in [dict(proof, problem_sha256='b'), dict(proof, encoding='shared-v2'),
                    dict(proof, steps=[dict(clause=[], hints=[2])]), dict(proof, steps=[])]:
            with self.assertRaises(ValueError):
                compact_certificate(problem, bad)
        for seconds in [0, -1, 601]:
            with self.assertRaises(ValueError):
                compact_certificate(problem, proof, seconds)
        with patch('producers.rup_compaction.time.monotonic', side_effect=[0, 2]):
            with self.assertRaisesRegex(ValueError, 'time budget'):
                compact_certificate(problem, proof, seconds=1)
