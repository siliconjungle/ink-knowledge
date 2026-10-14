import json, tempfile, unittest
from pathlib import Path
from ink_knowledge import Store, entry, identity
from ink_knowledge.implementation_candidates import identity_selection, publish_candidates

class Candidates(unittest.TestCase):
    def test_publication_preserves_existing_objects_names_and_imports_dependencies(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            dependency = entry('definition','test-data',{'value':3})
            dependency_id = identity(dependency)
            existing = Store.publish(root,[dependency],{'existing':dependency_id})
            existing.rebuild()
            package = identity_selection('1'*64)
            package['knowledge'] = existing.bundle([dependency_id])
            store, ids = publish_candidates(root,[package])
            bundle = store.bundle(ids)
            self.assertEqual(set(bundle['objects']), {ids[0],dependency_id})
            self.assertEqual(store.object(dependency_id),dependency)
            self.assertIn('existing',(root/'store/names.json').read_text())
            store.rebuild()
            self.assertEqual(store.bundle(ids),bundle)

    def test_names_only_update_during_candidate_preparation_is_preserved(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            objects = [entry('definition', 'test-data', {'value': n}) for n in [1, 2]]
            first, second = map(identity, objects)
            original = Store.publish(root, objects, {'chosen': first})
            def packages():
                # Candidate preparation runs after publish_candidates opens its
                # original Store. A names-only publication keeps the same root.
                concurrent = Store(root).extend([], {'chosen': second, 'new': second})
                self.assertEqual(concurrent.snapshot_id, original.snapshot_id)
                yield identity_selection('1' * 64)
            store, ids = publish_candidates(root, packages())
            self.assertEqual(json.loads((root / 'store/names.json').read_text()),
                             {'chosen': second, 'new': second})
            self.assertEqual(set(store.members()), {first, second, ids[0]})
            store.rebuild()
            self.assertEqual(store.object(ids[0])['kind'], 'implementation')

    def test_membership_change_during_candidate_preparation_reports_conflict(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            first = entry('definition', 'test-data', {'value': 1})
            second = entry('definition', 'test-data', {'value': 2})
            Store.publish(root, [first], {'chosen': identity(first)})
            def packages():
                Store(root).extend([second], {'chosen': identity(second)})
                yield identity_selection('1' * 64)
            with self.assertRaisesRegex(ValueError, 'publication changed during extension'):
                publish_candidates(root, packages())
            current = Store(root)
            self.assertEqual(set(current.members()), {identity(first), identity(second)})
            self.assertEqual(json.loads((root / 'store/names.json').read_text()),
                             {'chosen': identity(second)})

    def test_changed_dependency_bytes_fail_publication(self):
        with tempfile.TemporaryDirectory() as temporary:
            package = identity_selection('1'*64)
            package['knowledge']['objects']['2'*64] = entry('definition','test-data',{'value':3})
            with self.assertRaises(ValueError): publish_candidates(temporary,[package])

class SharedTopology(unittest.TestCase):
    def test_shared_views_preserve_existing_wide_leaves(self):
        with tempfile.TemporaryDirectory()as temporary:
            root=Path(temporary);objects=[entry('definition','test-data',{'value':n})for n in range(200)]
            Store.publish(root,objects)
            store,ids=publish_candidates(root,[identity_selection('1'*64)],shared_knowledge=True)
            self.assertGreater(max(len(w['entries'])for w in store.members().values()),2)
            self.assertEqual(len(store.members()),201)
            self.assertEqual(store.object(ids[0])['payload']['package']['knowledge_ref']['roots'],[])

if __name__ == '__main__': unittest.main()
