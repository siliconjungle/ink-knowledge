"""An unproved rewrite endpoint must not suppress another proof derivation."""
import os
import sqlite3
from contextlib import closing
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.contract_proofs import rewrite_proposals
from producers.semantic_laws import binary, law, value, var, word


class OrderedView:
    """Choose discovery order; objects and bundles retain real store authentication."""
    def __init__(self, store, rows):
        self.store, self.rows = store, rows

    def __getattr__(self, name):
        return getattr(self.store, name)

    def query(self, **query):
        return self.rows if query.get('operation') in (None, 'binary:+') else []

    def object(self, ident):
        return self.store.object(ident)

    def bundle(self, roots):
        return self.store.bundle(roots)


class ContractSearchAlternatives(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[2]
        cls.compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        cls.temporary = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.directory = Path(cls.temporary.name)
        source = cls.directory / 'source.ink'
        source.write_text('module alternatives;fn identity(x:u32)->u32{return x;}\n')
        cls.core = cls.directory / 'core.json'
        subprocess.run([cls.compiler, 'emit-core', source, '-o', cls.core],
                       check=True, capture_output=True, timeout=60)

    def fixture(self, directory, carrier='U32', nested=False, duplicate=False):
        x = var(value(carrier), 'x')
        start = binary('+', x, word(carrier, 0))
        # Both laws are true. The first has an extra premise that is unavailable
        # at this goal, so its use must reject without hiding the second law.
        conditional = semantic_entry(law({'x': x['sort']}, start, x,
            conditions=[{'from': x, 'to': word(carrier, 0)}]))
        unconditional = semantic_entry(law({'x': x['sort']}, start, x))
        store = Store.publish(directory, [conditional, unconditional])
        first, second = identity(conditional), identity(unconditional)
        rows = [first, first, second, second] if duplicate else [first, second]
        if nested:
            start = binary('*', start, word(carrier, 1))
        goal = dict(params={'x': x['sort']}, conditions=[], goal={'from': start, 'to': x})
        return goal, OrderedView(store, rows), (first, second)

    def replay(self, goal, proof, bundle):
        candidate = semantic_entry(law(goal['params'], goal['goal']['from'],
            goal['goal']['to'], proof, dependencies=bundle['roots']))
        with tempfile.TemporaryDirectory(dir=self.directory) as temporary:
            store = Store.publish(temporary, [*bundle['objects'].values(), candidate])
            view = Path(temporary) / 'view.json'
            view.write_bytes(canonical(store.bundle([identity(candidate)])))
            return subprocess.run([self.compiler, 'knowledge-check', self.core, view],
                                  capture_output=True, text=True, timeout=60)

    def test_rejected_premise_does_not_hide_valid_same_endpoint(self):
        for carrier in ['U32', 'U64']:
            for nested in [False, True]:
                with self.subTest(carrier=carrier, nested=nested), tempfile.TemporaryDirectory() as tmp:
                    goal, store, ids = self.fixture(tmp, carrier, nested)
                    proposals = list(rewrite_proposals(goal, store))
                    self.assertEqual({tuple(p[1]['roots']) for p in proposals}, {(ids[0],), (ids[1],)})
                    rejected = self.replay(goal, *proposals[0])
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertNotIn('identity mismatch', rejected.stderr)
                    valid = next(p for p in proposals if p[1]['roots'] == [ids[1]])
                    accepted = self.replay(goal, *valid)
                    self.assertEqual(accepted.returncode, 0, accepted.stderr)

    def test_duplicate_discovery_rows_do_not_duplicate_the_same_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            goal, store, ids = self.fixture(tmp, duplicate=True)
            proposals = list(rewrite_proposals(goal, store))
            self.assertEqual({tuple(p[1]['roots']) for p in proposals}, {(ids[0],), (ids[1],)})
            self.assertEqual(len(proposals), len({canonical(p) for p in proposals}))
            store.rows = list(ids)
            self.assertEqual(proposals, list(rewrite_proposals(goal, store)))

    def test_same_law_at_distinct_paths_remains_a_distinct_derivation(self):
        with tempfile.TemporaryDirectory() as tmp:
            x = var(value('U32'), 'x')
            short = binary('+', x, word('U32', 0))
            start = binary('+', short, word('U32', 0))
            obj = semantic_entry(law({'x': x['sort']}, short, x))
            store = Store.publish(tmp, [obj])
            goal = dict(params={'x': x['sort']}, conditions=[], goal={'from': start, 'to': x})
            proposals = list(rewrite_proposals(goal, OrderedView(store, [identity(obj)])))
            # Rewriting the outer or inner addition reaches the same expression,
            # using the same database root, but with different proof positions.
            first_steps = [p for p in proposals if p[0]['Trans']['middle'] == short]
            chains = {canonical(p[0]['Trans']['left']) for p in first_steps}
            self.assertEqual(len(chains), 2)
            for chain in chains:
                proposal = next(p for p in first_steps if canonical(p[0]['Trans']['left']) == chain)
                accepted = self.replay(goal, *proposal)
                self.assertEqual(accepted.returncode, 0, accepted.stderr)

    def test_specific_pattern_is_reached_before_broad_uses_exhaust_the_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            x = var(value('U32'), 'x')
            short = binary('+', x, word('U32', 0))
            start = binary('+', short, word('U32', 0))
            broad = [semantic_entry(law({'x': x['sort']}, short, x,
                conditions=[{'from': x, 'to': word('U32', n)}])) for n in range(12)]
            specific = semantic_entry(law({'x': x['sort']}, start, x))
            store = Store.publish(tmp, [*broad, specific])
            ordered = OrderedView(store, [identity(p) for p in [*broad, specific]])
            goal = dict(params={'x': x['sort']}, conditions=[], goal={'from': start, 'to': x})
            proposals = list(rewrite_proposals(goal, ordered, limit=1))
            self.assertEqual(len(proposals), 1)
            self.assertEqual(proposals[0][1]['roots'], [identity(specific)])
            accepted = self.replay(goal, *proposals[0])
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            # Ranking a specific law grants no authority to change the goal.
            forged = {**goal, 'goal': {'from': start, 'to': word('U32', 1)}}
            rejected = self.replay(forged, *proposals[0])
            self.assertNotEqual(rejected.returncode, 0)
            self.assertNotIn('identity mismatch', rejected.stderr)

    def test_legacy_acquisition_counts_scanned_rows_even_when_the_head_does_not_match(self):
        with tempfile.TemporaryDirectory() as tmp:
            x = var(value('U32'), 'x')
            start = binary('+', x, word('U32', 0))
            # The real operation index includes nested operations. These laws
            # mention addition, but have multiplication at their rewrite head.
            objects = []
            for n in range(1100):
                expression = binary('*', start, word('U32', n))
                objects.append(semantic_entry(law({'x': x['sort']}, expression, expression)))
            store = Store.publish(tmp, objects)
            store.rebuild()
            # Legacy discovery lacks head metadata, so all nested mentions
            # remain candidates. The fallback must still count every row.
            with closing(sqlite3.connect(store.root / 'index.sqlite')) as db, db:
                db.execute('DROP TABLE pattern_roots')
                db.execute('DROP TABLE pattern_targets')
            reads = []
            class CountedStore:
                root = store.root
                snapshot_id = store.snapshot_id
                def query(self, **query):
                    return store.query(**query)
                def object(self, ident):
                    reads.append(ident)
                    return store.object(ident)
                def bundle(self, roots):
                    return store.bundle(roots)
            goal = dict(params={'x': x['sort']}, conditions=[], goal={'from': start, 'to': x})
            self.assertEqual(list(rewrite_proposals(goal, CountedStore())), [])
            self.assertEqual(len(reads), 1024)

    def test_typed_head_discovery_reaches_a_valid_law_after_nested_mentions(self):
        with tempfile.TemporaryDirectory() as tmp:
            # A late content ID makes the scan-budget failure deterministic.
            for n in range(10000):
                name = f'x{n}'
                x = var(value('U32'), name)
                start = binary('+', x, word('U32', 0))
                useful = semantic_entry(law({name: x['sort']}, start, x))
                if identity(useful).startswith('ff'):
                    break
            else:
                self.fail('late fixture law not found')
            objects = []
            for n in range(1400):
                expr = binary('*', start, word('U32', n))
                objects.append(semantic_entry(law({name: x['sort']}, expr, expr)))
            objects.append(useful)
            store = Store.publish(tmp, objects)
            store.rebuild()
            self.assertGreater(sorted(map(identity, objects)).index(identity(useful)), 1024)
            reads = []
            class CountedStore:
                root = store.root
                snapshot_id = store.snapshot_id
                def query(self, **query):
                    return store.query(**query)
                def object(self, ident):
                    reads.append(ident)
                    return store.object(ident)
                def bundle(self, roots):
                    return store.bundle(roots)
            goal = dict(params={name: x['sort']}, conditions=[], goal={'from': start, 'to': x})
            proposals = list(rewrite_proposals(goal, CountedStore()))
            self.assertTrue(proposals)
            self.assertEqual(reads, [identity(useful)])
            accepted = self.replay(goal, *proposals[0])
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            forged = {**goal, 'goal': {'from': start, 'to': word('U32', 1)}}
            rejected = self.replay(forged, *proposals[0])
            self.assertNotEqual(rejected.returncode, 0)

    def test_explicit_pin_without_index_preserves_operation_filtered_fallback(self):
        with tempfile.TemporaryDirectory() as tmp:
            for n in range(10000):
                name = f'x{n}'
                x = var(value('U32'), name)
                start = binary('+', x, word('U32', 0))
                useful = semantic_entry(law({name: x['sort']}, start, x))
                if identity(useful).startswith('ff'):
                    break
            else:
                self.fail('late fixture law not found')
            objects = []
            for n in range(1400):
                expression = binary('*', x, word('U32', n))
                objects.append(semantic_entry(law({name: x['sort']}, expression, expression)))
            objects.append(useful)
            published = Store.publish(tmp, objects)
            pinned = Store(tmp, published.data / 'snapshots' / (published.snapshot_id + '.json'))
            self.assertFalse((pinned.root / 'index.sqlite').exists())
            goal = dict(params={name: x['sort']}, conditions=[], goal={'from': start, 'to': x})
            proposals = list(rewrite_proposals(goal, pinned))
            self.assertTrue(proposals)
            self.assertEqual(proposals[0][1]['roots'], [identity(useful)])
            self.assertFalse((pinned.root / 'index.sqlite').exists())
            self.assertEqual(self.replay(goal, *proposals[0]).returncode, 0)

    def test_proposal_budget_remains_a_bound_even_when_alternatives_exist(self):
        with tempfile.TemporaryDirectory() as tmp:
            goal, store, ids = self.fixture(tmp, duplicate=True)
            self.assertEqual(list(rewrite_proposals(goal, store, limit=0)), [])
            proposals = list(rewrite_proposals(goal, store, limit=1))
            self.assertEqual(len(proposals), 1)
            self.assertEqual(proposals[0][1]['roots'], [ids[0]])
            self.assertNotEqual(self.replay(goal, *proposals[0]).returncode, 0)


if __name__ == '__main__':
    unittest.main()
