"""Query reuse preserves semantic facts, resource limits and caller lifetimes."""
import gc
import unittest
import weakref
from unittest.mock import patch
from producers import word_facts as facts
from producers.semantic_laws import value, var, word, op, term
from . import test_word_facts


class BatchedWordFacts(test_word_facts.WordFacts):
    """Run the independent value oracle through the combined-query API too."""
    def setUp(self):
        a = patch.object(test_word_facts, 'analyse', lambda source: facts.analyse_candidates(source)[0])
        c = patch.object(test_word_facts, 'candidates', lambda source: iter(facts.analyse_candidates(source)[1]))
        a.start(); c.start()
        self.addCleanup(a.stop); self.addCleanup(c.stop)


class WordFactQueries(unittest.TestCase):
    def setUp(self):
        self.sort = value('U32')
        self.x = var(self.sort, 'x')

    def wrap(self, source, depth):
        for _ in range(depth):
            source = op(self.sort, 'call:word_or', source, word('U32', 1))
        return source

    def outcome(self, source, **kwargs):
        try:
            return facts.analyse(source, **kwargs)
        except ValueError as error:
            return str(error)

    def test_warm_cache_charges_original_visits_and_relative_depth(self):
        inner = self.wrap(self.x, 40)
        for extra in [0, 23, 24, 25, 30]:
            source = self.wrap(inner, extra)
            memo = facts._FactMemo()
            facts.analyse(inner, _memo=memo)
            for budget in [0, 1, 2, 16, 64, 128, 4096]:
                with self.subTest(depth=40+extra, budget=budget):
                    self.assertEqual(self.outcome(source, max_nodes=budget),
                                     self.outcome(source, max_nodes=budget, _memo=memo))

    def test_same_expression_in_distinct_scopes_never_reuses_other_branch_facts(self):
        source = op(self.sort, 'call:word_and', self.x, word('U32', 127))
        memo = facts._FactMemo()
        contexts = [[], [(self.x, facts.Facts(32, minimum=0, maximum=63))],
                    [(self.x, facts.Facts(32, minimum=64, maximum=127))],
                    [(self.x, facts.Facts(32)), (self.x, facts.constant(32, 9))]]
        for scope in contexts + contexts[::-1]:
            self.assertEqual(facts.analyse(source, _scope=scope),
                             facts.analyse(source, _scope=scope, _memo=memo))

    def test_exhausted_cache_limits_fall_back_without_losing_facts(self):
        source = self.wrap(self.x, 20)
        for limit in [dict(max_entries=0), dict(max_entries=2),
                      dict(max_cells=2), dict(max_charge=1024)]:
            with self.subTest(limit=limit):
                memo = facts._FactMemo(**limit)
                self.assertEqual(facts.analyse(source), facts.analyse(source, _memo=memo))
                self.assertLessEqual(len(memo.entries), memo.max_entries)
                self.assertLessEqual(memo.cells, memo.max_cells)
                self.assertLessEqual(memo.charge, memo.max_charge)

    def test_identity_subjects_are_retained_only_until_query_cleanup(self):
        class WeakDict(dict):
            pass
        subject = WeakDict(var(self.sort, 'subject'))
        source = WeakDict(self.wrap(self.x, 1))
        subject_ref, source_ref = weakref.ref(subject), weakref.ref(source)
        memo = facts._FactMemo()
        facts.analyse(source, _scope=[(subject, facts.Facts(32))], _memo=memo)
        del subject, source
        gc.collect()
        self.assertIsNotNone(subject_ref()); self.assertIsNotNone(source_ref())
        memo.clear(); gc.collect()
        self.assertIsNone(subject_ref()); self.assertIsNone(source_ref())

    def test_no_cached_fact_crosses_streaming_yield_or_separate_query(self):
        left = word('U32', 1)
        source = op(self.sort, 'call:word_and', left, word('U32', 3))
        with patch.object(facts, '_FactMemo', side_effect=AssertionError('stream cache')):
            iterator = facts.candidates(source)
            self.assertEqual(next(iterator)[0], 'constant-from-bits-or-range')
            left['node']['Word'] = 8
            self.assertEqual(list(iterator), [])
        self.assertEqual(facts.analyse_candidates(source)[0].constant, 0)
        left['node']['Word'] = 2
        self.assertEqual(facts.analyse_candidates(source)[0].constant, 2)

    def test_cleanup_after_success_and_rejected_query(self):
        created = []
        original = facts._FactMemo
        def memo():
            result = original(); created.append(result); return result
        with patch.object(facts, '_FactMemo', side_effect=memo):
            facts.analyse_candidates(self.wrap(self.x, 3))
            with self.assertRaisesRegex(ValueError, 'budget'):
                facts.analyse_candidates(self.wrap(self.x, 65))
        self.assertEqual(len(created), 2)
        for result in created:
            self.assertFalse(result.entries)
            self.assertEqual((result.cells, result.charge), (0, 0))

    def test_unsupported_carriers_and_calls_do_not_acquire_assumptions(self):
        text = term(value('String'), {'String': 'opaque'})
        source = op(self.sort, 'call:opaque', text)
        result, proposals = facts.analyse_candidates(source)
        self.assertEqual(result, facts.Facts(32)); self.assertEqual(proposals, [])
        with self.assertRaisesRegex(ValueError, 'unsigned words and Bool'):
            facts.analyse_candidates(text)


if __name__ == '__main__':
    unittest.main()
