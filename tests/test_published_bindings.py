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


class IndexedPublishedBindings(unittest.TestCase):
    def test_complete_index_filters_without_loading_bodies_and_keeps_historical_pins(self):
        from unittest.mock import patch
        from ink_knowledge import identity
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);first=implementation('a'*64,1);second=implementation('b'*64,2)
            store=Store.publish(root,[first,second]);store.rebuild();old=Store(root,store.data/'snapshots'/(store.snapshot_id+'.json'))
            with patch.object(Store,'object',side_effect=AssertionError('unused body loaded')):
                self.assertEqual(sorted(b for _,b in bindings(store)['implementation']),['a'*64,'b'*64])
            extended=store.extend([implementation('a'*64,3)]);extended.refresh_index()
            with patch.object(Store,'object',side_effect=AssertionError('unused body loaded')):
                self.assertEqual(len(bindings(extended)['implementation']),3)
                self.assertEqual(len(bindings(old)['implementation']),2)
            # A forged source-binding hint cannot turn a package for B into A.
            import sqlite3
            with sqlite3.connect(root/'index.sqlite') as db:
                db.execute('UPDATE published_bindings_v1 SET binding=? WHERE entry_id=?',('a'*64,identity(second)))
            rows=list(published(dict(knowledge_root=str(root),source='a'*64,model=dict(objects=[]))))
            self.assertEqual(len([r for r in rows if r['status']=='proposal']),2)
            with sqlite3.connect(root/'index.sqlite') as db:
                db.execute('UPDATE published_bindings_v1 SET kind=?,binding=? WHERE entry_id=?',('representation',source_key([]),identity(first)))
            rows=list(published(dict(knowledge_root=str(root),source='a'*64,model=dict(objects=[]))))
            self.assertEqual(len([r for r in rows if r['status']=='proposal']),1)

    def test_legacy_metadata_migrates_once_in_place_and_missing_rows_fall_back(self):
        import sqlite3
        from unittest.mock import patch
        from ink_knowledge.published_bindings import indexed
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);store=Store.publish(root,[implementation('a'*64,1),implementation('b'*64,2)]);store.rebuild()
            with sqlite3.connect(root/'index.sqlite') as db:db.execute('DROP TABLE published_bindings_v1')
            self.assertIsNone(indexed(store))
            with patch('ink_knowledge.index_cache.copy',side_effect=AssertionError('whole database copy')):
                self.assertTrue(store.ensure_index())
            self.assertEqual(len(indexed(store)['implementation']),2)
            with patch.object(Store,'_read_object',side_effect=AssertionError('repeated canonical migration')):
                self.assertFalse(store.ensure_index());self.assertEqual(len(bindings(store)['implementation']),2)
            with sqlite3.connect(root/'index.sqlite') as db:db.execute('DELETE FROM published_bindings_v1')
            self.assertIsNone(indexed(store));self.assertEqual(len(bindings(store)['implementation']),2)

    def test_authenticated_false_package_still_requires_ordinary_kernel_admission(self):
        import os,subprocess
        from ink_knowledge import canonical,identity,semantic_entry
        from producers.semantic_laws import law,value,var,binary,word
        repo=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',repo/'target/debug/ink')).resolve()
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);source=d/'source.ink';source.write_text('module binding_hints;pub fn unrelated(payload:u32)->u32{return payload+1;}')
            r=subprocess.run([compiler,'emit-core',source,'-o',d/'core.json'],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
            r=subprocess.run([compiler,'check-core',d/'core.json'],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr);source_hash=json.loads(r.stdout)['core_sha256']
            s=value('U32');x=var(s,'payload');false=semantic_entry(law({'payload':s},binary('+',x,word('U32',1)),x));fid=identity(false);proofs=Store.publish(d/'proofs',[false]);package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=source_hash,knowledge=proofs.bundle([fid]),applications=[dict(function='unrelated',path=[],law=fid,arguments={'payload':x},premises=[])])
            candidate=entry('implementation','ink-implementation-candidate-v1',dict(package=package));store=Store.publish(d/'knowledge',[candidate]);store.rebuild();rows=list(published(dict(knowledge_root=str(store.root),source=source_hash,model=dict(objects=[]))));self.assertEqual(len(rows),1)
            path=d/'selection.json';path.write_bytes(canonical(rows[0]['step']['package']));r=subprocess.run([compiler,'check-selection',d/'core.json',path],capture_output=True,text=True,timeout=120);self.assertNotEqual(r.returncode,0);self.assertNotIn('membership',r.stderr.lower())


class DefensiveBindingMetadata(unittest.TestCase):
    def test_malformed_optional_bindings_do_not_block_unrelated_entries(self):
        from ink_knowledge.published_bindings import build
        with tempfile.TemporaryDirectory() as d:
            objects=[implementation('a'*64,1),
                     entry('implementation','unknown-protocol-v1',dict(package=dict(input_core_sha256={'untrusted':'object'}))),
                     entry('representation','unknown-protocol-v1',dict(source_objects=17)),
                     entry('representation','unknown-protocol-v1',dict(source_objects=['a',17]))]
            store=Store.publish(d,objects);store.rebuild();cached=bindings(store)
            self.assertEqual(cached,build(store)['entries'])
            self.assertEqual([key for _,key in cached['representation']],[None,None])
            rows=list(published(dict(knowledge_root=d,source='a'*64,model=dict(objects=[]))))
            self.assertEqual(len([r for r in rows if r['status']=='proposal']),1)

    def test_missing_kind_index_migrates_in_place_with_query_and_pin_parity(self):
        import sqlite3
        from unittest.mock import patch
        from ink_knowledge import identity
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);a=implementation('a'*64,1);b=implementation('b'*64,2);store=Store.publish(root,[a,b]);store.rebuild();before=store.query(kind='implementation');pin=store.snapshot_id
            with sqlite3.connect(root/'index.sqlite') as db:db.execute('DROP INDEX entry_kind_lookup')
            with patch('ink_knowledge.index_cache.copy',side_effect=AssertionError('whole database copy')):self.assertTrue(store.ensure_index())
            self.assertEqual(store.query(kind='implementation'),before);self.assertEqual(store.snapshot_id,pin)
            self.assertEqual(store.query(kind='implementation',after=before[0]),before[1:]);self.assertEqual(store.query(kind='implementation',limit=1),before[:1]);self.assertEqual(store.query(kind='representation'),[])
            with sqlite3.connect(root/'index.sqlite') as db:
                plan=db.execute('EXPLAIN QUERY PLAN SELECT id FROM entries WHERE kind=? ORDER BY id',('implementation',)).fetchall()
                self.assertTrue(any('entry_kind_lookup'in row[-1]for row in plan),plan)

if __name__=='__main__':unittest.main()
