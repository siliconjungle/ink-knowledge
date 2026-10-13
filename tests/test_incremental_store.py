import json, tempfile, unittest
from pathlib import Path
from unittest.mock import patch
from ink_knowledge import Store, entry, identity

class IncrementalStore(unittest.TestCase):
    def test_local_publication_and_historical_witnesses(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);items=[entry('definition','test-v1',{'body':i}) for i in range(3000)]
            old=Store.publish(root,items);old.rebuild();old_id=old.snapshot_id
            before={p.stem for p in (root/'store/trees').glob('*.json')}
            extra=entry('definition','test-v1',{'body':'extra'})
            new=Store.publish(root,[*items,extra]);after={p.stem for p in (root/'store/trees').glob('*.json')}
            self.assertLessEqual(len(after-before),8) # one leaf and a six-level bucket path
            with patch.object(new,'_read_object',wraps=new._read_object) as reads:
                self.assertEqual(new.refresh_index(),1)
                self.assertEqual([call.args[0] for call in reads.call_args_list],[identity(extra)])
            pinned=Store(root,root/'store/snapshots'/f'{old_id}.json')
            self.assertEqual(len(pinned.members()),3000)
            for obj in [items[0],items[-1],extra]:self.assertEqual(new.object(identity(obj)),obj)
            self.assertEqual(pinned.object(identity(items[0])),items[0])
            self.assertEqual(new.query(kind='definition',limit=1024),sorted(new.members())[:1024])
            new.rebuild();self.assertEqual(new.query(kind='definition',limit=1024),sorted(new.members())[:1024])

    def test_failed_refresh_preserves_previous_index_and_exports_reauthenticate(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);a=entry('definition','test-v1',{'body':'a'});b=entry('definition','test-v1',{'body':'b'})
            old=Store.publish(root,[a]);old.rebuild();before=(root/'index.sqlite').read_bytes()
            new=Store.publish(root,[a,b]);path=root/'store/objects'/f'{identity(b)}.json';original=path.read_bytes()
            path.write_text(json.dumps({**b,'semantics':'forged'}))
            with self.assertRaisesRegex(ValueError,'content mismatch'):new.refresh_index()
            self.assertEqual((root/'index.sqlite').read_bytes(),before)
            path.write_bytes(original);self.assertEqual(new.refresh_index(),1)
            (root/'store/objects'/f'{identity(a)}.json').write_text(json.dumps({**a,'semantics':'forged'}))
            self.assertEqual(new.refresh_index(),0) # disposable discovery rows are hints
            with self.assertRaisesRegex(ValueError,'content mismatch'):new.bundle([identity(a)])
            self.assertEqual(list(root.glob('.ink-index-*')),[])

    def test_empty_tier_boundaries_and_bucket_overflow(self):
        with tempfile.TemporaryDirectory() as tmp:
            items=[entry('definition','test-v1',{'body':i}) for i in range(257)]
            for count in [0,1,64,65,128,129,256,257]:
                store=Store.publish(tmp,items[:count]);store.refresh_index()
                self.assertEqual(set(store.members()),{identity(o) for o in items[:count]})
                for obj in items[:count]:self.assertEqual(store.object(identity(obj)),obj)
            # Force a skewed prefix without forging any hashes; local leaves split.
            skew=[];i=0
            while len(skew)<129:
                obj=entry('definition','test-v1',{'body':['skew',i]});i+=1
                if identity(obj).startswith('0'):skew.append(obj)
            store=Store.publish(tmp,skew);self.assertEqual(len(store.members()),129)
            self.assertTrue(all(len(w['entries'])<=64 for w in store.members().values()))

class AppendPublication(unittest.TestCase):
    def test_extension_reuses_old_references_but_still_authenticates_retrieval(self):
        from unittest.mock import patch
        from ink_knowledge.store import entry,identity
        with tempfile.TemporaryDirectory()as temporary:
            root=Path(temporary)
            first=entry('definition','test-v1',{'body':1});a=identity(first)
            old=Store.publish(root,[first],{'first':a});pin=old.snapshot_id
            second=entry('definition','test-v1',{'body':2},[a]);b=identity(second)
            with patch.object(Store,'object',side_effect=AssertionError('reopened old proof body')):
                new=old.extend([second],{'second':b})
            self.assertEqual(json.loads((root/'store/names.json').read_text()),{'first':a,'second':b})
            self.assertEqual(set(new.bundle([b])['objects']),{a,b})
            self.assertEqual(set(Store(root,root/'store/snapshots'/(pin+'.json')).members()),{a})
            (root/'store/objects'/(a+'.json')).write_text(json.dumps({**first,'payload':{'body':99}}))
            with self.assertRaises(ValueError):new.bundle([b])
    def test_failed_extensions_do_not_publish_a_new_pointer(self):
        from ink_knowledge.store import entry,identity
        with tempfile.TemporaryDirectory()as temporary:
            root=Path(temporary);first=entry('definition','test-v1',{'body':1});store=Store.publish(root,[first]);pin=store.snapshot_id
            missing=entry('definition','test-v1',{'body':2},['1'*64])
            with self.assertRaises(ValueError):store.extend([missing])
            self.assertEqual(Store(root).snapshot_id,pin)
            frozen=Store(root,root/'store/snapshots'/(pin+'.json'))
            with self.assertRaises(ValueError):frozen.extend([])

class PublicationReuse(unittest.TestCase):
 def test_constructed_tree_is_reused_but_later_instances_authenticate_files(self):
  from ink_knowledge import store as module
  with tempfile.TemporaryDirectory() as tmp:
   objects=[entry('definition','test',{'number':n})for n in range(200)]
   original=module.read
   with patch.object(module,'read',wraps=original)as reads:
    published=Store.publish(tmp,objects)
   self.assertFalse(any('/trees/'in str(c.args[0])for c in reads.call_args_list))
   members=published.members();leaf=next(iter(members.values()))
   for ident in leaf['entries']:self.assertIs(members[ident],leaf)
   root=Path(tmp);tree=root/'store/trees'/(published.snapshot['root']+'.json');value=json.loads(tree.read_text());value['left']='0'*64;tree.write_text(json.dumps(value))
   with self.assertRaisesRegex(ValueError,'tree content mismatch'):Store(root).members()
 def test_duplicate_extension_is_a_noop_and_preserves_all_names(self):
  with tempfile.TemporaryDirectory()as tmp:
   obj=entry('definition','test',{'number':1});ident=identity(obj);store=Store.publish(tmp,[obj],{'a':ident})
   with patch.object(Store,'_publish_ids',side_effect=AssertionError('republished unchanged tree')):
    self.assertIs(store.extend([obj]),store)
   changed=store.extend([obj],{'b':ident});self.assertEqual(changed.snapshot_id,store.snapshot_id)
   self.assertEqual(json.loads((Path(tmp)/'store/names.json').read_text()),{'a':ident,'b':ident})

class AtomicModernRefresh(unittest.TestCase):
 def test_late_failure_rolls_back_rows_and_keeps_pinned_exports(self):
  from ink_knowledge import template_index
  with tempfile.TemporaryDirectory()as tmp:
   a=entry('definition','test',{'value':1});b=entry('definition','test',{'value':2})
   old=Store.publish(tmp,[a]);old.rebuild();before=(Path(tmp)/'index.sqlite').read_bytes();expected=old.bundle([identity(a)])
   new=old.extend([b])
   with patch.object(template_index,'refresh',side_effect=ValueError('late refresh failure')):
    with self.assertRaisesRegex(ValueError,'late refresh failure'):new.refresh_index()
   self.assertEqual((Path(tmp)/'index.sqlite').read_bytes(),before)
   self.assertEqual(old.bundle([identity(a)]),expected)
   with patch('ink_knowledge.index_cache.copy',side_effect=AssertionError('copied modern index')):
    self.assertEqual(new.refresh_index(),1)
   self.assertEqual(old.bundle([identity(a)]),expected)
   self.assertEqual(new.object(identity(b)),b)
