from contextlib import closing
import copy,json,sqlite3,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,entry,identity,canonical
class StoreTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        self.a=entry('definition','test-v1',dict(body='a'),parameters={'x':'U32'},result='U32')
        self.b=entry('theorem','test-v1',dict(body='b'),[identity(self.a)],conditions=[{'from':1,'to':1}])
        self.store=Store.publish(self.root,[self.a,self.b],{'a':identity(self.a)})
    def tearDown(self):self.temp.cleanup()
    def test_canonical_identity_is_key_order_independent_and_rejects_floats(self):
        self.assertEqual(identity({'b':2,'a':1}),identity({'a':1,'b':2}))
        self.assertEqual(canonical({'a':True}),b'{"a":true}')
        with self.assertRaises(ValueError):canonical({'a':1.0})
    def test_subset_has_exact_dependency_closure_and_rebuildable_queries(self):
        self.store.rebuild();self.assertEqual(self.store.query(parameter_type='U32'),[identity(self.a)])
        self.assertEqual(self.store.query(condition={'to':1,'from':1}),[identity(self.b)])
        fresh=Store(self.root);view=fresh.bundle([identity(self.b)])
        self.assertIsNone(fresh._members) # Fetching a subset does not scan the snapshot tree.
        self.assertEqual(set(view['objects']),{identity(self.a),identity(self.b)})
        (self.root/'index.sqlite').unlink();self.assertEqual(self.store.query(kind='theorem'),[identity(self.b)])
    def test_index_forgery_cannot_supply_membership_authority(self):
        self.store.rebuild()
        with closing(sqlite3.connect(self.root/'index.sqlite')) as db,db:
            db.execute('UPDATE members SET witness=?',(json.dumps({'entries':['0'*64],'path':[]}),))
        with self.assertRaises(ValueError):Store(self.root).bundle([identity(self.a)])
    def test_tampered_content_and_missing_dependencies_are_rejected(self):
        i=identity(self.a);p=self.root/'store/objects'/f'{i}.json'
        p.write_text(json.dumps({**self.a,'semantics':'forged'}))
        with self.assertRaises(ValueError):Store(self.root).bundle([i])
        with self.assertRaises(ValueError):Store.publish(self.root,[self.b])
    def test_pinned_snapshot_survives_publication_and_index_staleness_is_explicit(self):
        original=self.store.snapshot_id;self.store.rebuild()
        c=entry('definition','test-v1',dict(body='c'))
        newer=Store.publish(self.root,[self.a,self.b,c]);self.assertNotEqual(original,newer.snapshot_id)
        with self.assertRaises(ValueError):newer.query()
        old=Store(self.root,self.root/'store/snapshots'/f'{original}.json')
        self.assertEqual(old.query(kind='theorem'),[identity(self.b)])
        self.assertEqual(set(old.bundle([identity(self.b)])['objects']),{identity(self.a),identity(self.b)})
    def test_multilevel_membership_and_separate_observations(self):
        objects=[entry('definition','test-v1',dict(body=i)) for i in range(193)]
        s=Store.publish(self.root,objects);s.rebuild()
        self.assertTrue(all(len(s.witness(identity(o))['path'])==2 for o in objects))
        obs=dict(schema=1,program='1'*64,entries=[identity(objects[0])],plan='2'*64,
                 target=dict(hardware='test',driver='test',toolchain='test',backend='cpu',bridge='host'),
                 workload=dict(shape=[100],distribution='zeros',concurrency=1,residency='host'),
                 metrics=dict(complete_call_ns=['100','200'],peak_bytes=400))
        pin=s.snapshot_id;i=s.observe(obs);self.assertEqual(s.snapshot_id,pin)
        self.assertEqual(s.observations(obs['program'],[obs['plan']],obs['target'],obs['workload']),[obs])
        with closing(sqlite3.connect(self.root/'index.sqlite')) as db,db:self.assertEqual(db.execute('SELECT id FROM observations').fetchone()[0],i)
        with self.assertRaises(ValueError):s.object(i)
if __name__=='__main__':unittest.main()
