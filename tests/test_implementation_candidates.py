import tempfile, unittest
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
