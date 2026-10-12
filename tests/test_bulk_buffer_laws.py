import json,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.bulk_buffer_laws import examples,publish
from producers.semantic_laws import value,var,law
class BulkBufferPublication(unittest.TestCase):
    def test_publication_is_idempotent_and_helpers_are_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);v=var(value('U32'),'v');seed=semantic_entry(law({'v':v['sort']},v,v));i=identity(seed)
            store=Store.publish(root,[seed],{})
            (root/'store/rewrite-view.json').write_bytes(canonical(store.bundle([i]))+b'\n')
            first=publish(root);snapshot=first.snapshot_id;view=(root/'store/bulk-buffer-view.json').read_bytes()
            second=publish(root)
            self.assertEqual(second.snapshot_id,snapshot);self.assertEqual(view,(root/'store/bulk-buffer-view.json').read_bytes())
            installed=json.loads((root/'store/rewrite-view.json').read_text())['roots']
            self.assertEqual(len(installed),41)
            names=json.loads((root/'store/names.json').read_text())
            for name,entry in examples().items():
                entry_id=names['rewrite/'+name];self.assertEqual(second.object(entry_id),semantic_entry(entry))
                self.assertEqual(entry_id in installed,not name.endswith('-helper'))
    def test_all_laws_have_closed_authenticated_dependencies(self):
        entries={identity(semantic_entry(x)):x for x in examples().values()}
        self.assertEqual(len(entries),48)
        for entry in entries.values():self.assertTrue(set(entry['dependencies'])<=set(entries))
if __name__=='__main__':unittest.main()
