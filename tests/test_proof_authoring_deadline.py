import time
import unittest
from producers.bitvector_proofs import HintBuilder, certificate


class ProofAuthoringDeadline(unittest.TestCase):
    def test_expired_budget_stops_hint_generation_after_solver_phase(self):
        builder=HintBuilder([[1],[-1]])
        self.assertTrue(builder.hints([]))
        builder.deadline=time.monotonic()-1
        with self.assertRaisesRegex(ValueError,'total time budget'):builder.hints([])
        with self.assertRaisesRegex(ValueError,'total time budget'):builder.add([2])

    def test_small_contradiction_completes_with_a_bounded_budget(self):
        problem=dict(clauses=[[1],[-1]],sha256='test-obligation')
        proof=certificate(problem,seconds=1,total_seconds=1)
        self.assertEqual(proof['steps'][-1]['clause'],[])
        self.assertNotIn('encoding',proof)
        shared=certificate(dict(problem,encoding='shared-v2'),seconds=1,total_seconds=1)
        self.assertEqual(shared['encoding'],'shared-v2')
        for invalid in (0,-1,601):
            with self.assertRaises(ValueError):certificate(problem,total_seconds=invalid)


if __name__=='__main__':unittest.main()
