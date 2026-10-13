"""The published-package binding index is a per-snapshot filter, never authority."""
import json,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store
from ink_knowledge.store import entry
from ink_knowledge.published_bindings import bindings,source_key,NAME
from producers.planning_recipes import published

def implementation(source,tag):
    package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=source,applications=[],
                 knowledge=dict(schema=1,snapshot=dict(schema=1,semantics='ink-knowledge-snapshot-v1',root='0'*64),roots=[],objects={},membership={}),tag=tag)
    return entry('implementation','ink-implementation-candidate-v1',dict(package=package))

class PublishedBindings(unittest.TestCase):
    def test_filter_matches_a_full_scan_and_rebuilds_for_a_new_snapshot(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            store=Store.publish(root,[implementation('a'*64,1),implementation('b'*64,2),
                                      entry('maintenance','ink-test-maintenance-v1',dict(note='no package'))])
            first=bindings(store)
            self.assertEqual(sorted(b for _,b in first['implementation']),['a'*64,'b'*64])
            self.assertEqual([b for _,b in first['maintenance']],[None])
            rows=list(published(dict(knowledge_root=str(root),source='a'*64,model=dict(objects=[]))))
            self.assertEqual([r['status'] for r in rows].count('proposal'),1)
            self.assertEqual([r['status'] for r in rows].count('declined'),1)
            self.assertEqual(json.loads((root/NAME).read_text())['snapshot'],store.snapshot_id)
            extended=store.extend([implementation('a'*64,3)])
            self.assertEqual(len([b for _,b in bindings(extended)['implementation'] if b=='a'*64]),2)
            self.assertEqual(json.loads((root/NAME).read_text())['snapshot'],extended.snapshot_id)
    def test_representation_keys_ignore_object_order(self):
        self.assertEqual(source_key(['b','a']),source_key(['a','b']))

if __name__=='__main__':unittest.main()
