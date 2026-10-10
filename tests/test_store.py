from contextlib import closing
import copy,json,sqlite3,tempfile,unittest
from unittest.mock import patch
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
    def test_bundle_reuses_one_connection_and_leaf_authentication_with_exact_output(self):
        self.store.rebuild();fresh=Store(self.root)
        from ink_knowledge.store import read
        with patch('ink_knowledge.store.sqlite3.connect',wraps=sqlite3.connect) as connects, \
             patch('ink_knowledge.store.read',wraps=read) as reads, \
             patch('ink_knowledge.store.identity',wraps=identity) as hashes:
            view=fresh.bundle([identity(self.b),identity(self.b)])
        self.assertEqual(connects.call_count,1)
        self.assertEqual(reads.call_count,2)
        self.assertEqual(sum(set(call.args[0])=={'schema','entries'} for call in hashes.call_args_list),1)
        self.assertIsNone(fresh._members)
        self.assertEqual(canonical(view),canonical(self.store.bundle([identity(self.b)])))
        self.assertEqual(set(view['objects']),{identity(self.a),identity(self.b)})
        # Reauthentication is scoped to a call, not cached across later exports.
        with closing(sqlite3.connect(self.root/'index.sqlite')) as db,db:
            db.execute('UPDATE members SET witness=? WHERE entry_id=?',
                       (json.dumps({'entries':['0'*64],'path':[]}),identity(self.b)))
        with self.assertRaisesRegex(ValueError,'membership proof'):
            fresh.bundle([identity(self.b)])
        self.store.rebuild()
        (self.root/'store/objects'/f'{identity(self.a)}.json').write_text(json.dumps({**self.a,'semantics':'forged'}))
        with self.assertRaisesRegex(ValueError,'content mismatch'):
            fresh.bundle([identity(self.b)])
    def test_authenticated_leaf_reuse_cannot_admit_an_unlisted_entry(self):
        self.store.rebuild();aid=identity(self.a)
        # Ensure the genuine member is visited first, populating the local cache.
        number=0
        while True:
            forged=entry('definition','test-v1',dict(body=['unlisted',number]));fid=identity(forged)
            if fid>aid:break
            number+=1
        (self.root/'store/objects'/f'{fid}.json').write_bytes(canonical(forged)+b'\n')
        with closing(sqlite3.connect(self.root/'index.sqlite')) as db,db:
            witness=db.execute('SELECT witness FROM members WHERE entry_id=?',(aid,)).fetchone()[0]
            db.execute('INSERT INTO entries VALUES(?,?,?,?,?,?)',(fid,forged['kind'],forged['semantics'],'null','{}','[]'))
            db.execute('INSERT INTO members VALUES(?,?,?)',(self.store.snapshot_id,fid,witness))
        with self.assertRaisesRegex(ValueError,'membership proof'):
            Store(self.root).bundle([aid,fid])
    def test_bundle_uses_one_read_snapshot_during_concurrent_index_updates(self):
        self.store.rebuild();fresh=Store(self.root);index=self.root/'index.sqlite'
        expected=self.store.bundle([identity(self.b)])
        with closing(sqlite3.connect(index)) as db:
            db.execute('PRAGMA journal_mode=WAL')
        original=fresh._read_object;changed=False
        def read_with_update(i):
            nonlocal changed
            if not changed:
                changed=True
                with closing(sqlite3.connect(index,timeout=0)) as db,db:
                    db.execute('DELETE FROM members WHERE entry_id=?',(identity(self.a),))
            return original(i)
        with patch.object(fresh,'_read_object',side_effect=read_with_update):
            self.assertEqual(canonical(fresh.bundle([identity(self.b)])),canonical(expected))
        with self.assertRaisesRegex(ValueError,'absent from indexed snapshot'):
            fresh.bundle([identity(self.b)])
    def test_bundle_preserves_depth_and_object_limits_and_closes_failed_exports(self):
        objects=[]
        for number in range(66):
            objects.append(entry('definition','test-v1',dict(body=number),[identity(objects[-1])] if objects else []))
        store=Store.publish(self.root,objects);store.rebuild()
        self.assertEqual(len(Store(self.root).bundle([identity(objects[-2])])['objects']),65)
        with self.assertRaisesRegex(ValueError,'dependency closure limit'):
            Store(self.root).bundle([identity(objects[-1])])
        # A failed read transaction must not retain a lock on the disposable index.
        with closing(sqlite3.connect(self.root/'index.sqlite',timeout=0)) as db,db:
            db.execute('DELETE FROM names')
        leaves=[entry('definition','test-v1',dict(body=['leaf',i])) for i in range(1024)]
        parents=[entry('definition','test-v1',dict(body=['parent',i]),[identity(x) for x in leaves[i:i+128]]) for i in range(0,1024,128)]
        root=entry('definition','test-v1',dict(body='root'),[identity(x) for x in parents])
        store=Store.publish(self.root,[*leaves,*parents,root]);store.rebuild()
        with self.assertRaisesRegex(ValueError,'dependency closure limit'):
            Store(self.root).bundle([identity(root)])
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
    def test_unmeasured_memory_survives_observation_rebuild_without_becoming_zero(self):
        obs=dict(schema=1,program='1'*64,entries=[identity(self.a)],plan='2'*64,
                 target=dict(hardware='test',driver='test',toolchain='test',backend='cpu',bridge='three-call'),
                 workload=dict(shape={'rows':48,'action':'get'},distribution='nonzero keys',concurrency=1,residency='host'),
                 metrics=dict(complete_call_ns=['54000','55000'],peak_bytes=None))
        pin=self.store.snapshot_id;self.store.rebuild();unknown=self.store.observe(obs)
        zero=copy.deepcopy(obs);zero['metrics']['peak_bytes']=0;measured=self.store.observe(zero)
        self.assertNotEqual(unknown,measured)
        self.assertEqual(self.store.snapshot_id,pin)
        (self.root/'index.sqlite').unlink()
        replay=Store(self.root).observations(obs['program'],[obs['plan']],obs['target'],obs['workload'])
        self.assertEqual({identity(o) for o in replay},{unknown,measured})
        self.assertEqual(next(o for o in replay if identity(o)==unknown)['metrics']['peak_bytes'],None)
        other=copy.deepcopy(obs['target']);other['bridge']='fused'
        self.assertEqual(self.store.observations(obs['program'],[obs['plan']],other,obs['workload']),[])
        for bad in [-1,False,'0',0.0]:
            invalid=copy.deepcopy(obs);invalid['metrics']['peak_bytes']=bad
            with self.assertRaises(ValueError):self.store.observe(invalid)
    def test_cost_lookup_filters_plans_before_limit_and_reads_only_selected_files(self):
        obs=dict(schema=1,program='1'*64,entries=[identity(self.a)],plan='2'*64,
                 target=dict(hardware='test',driver='test',toolchain='test',backend='cpu',bridge='host'),
                 workload=dict(shape=[48],distribution='test',concurrency=1,residency='host'),
                 metrics=dict(complete_call_ns=['100'],peak_bytes=None))
        self.store.rebuild()
        records=[]
        for number in range(32):
            value=copy.deepcopy(obs);value['plan']=identity({'candidate':number})
            records.append((self.store.observe(value),value))
        records.sort(key=lambda record:record[0]);selected=records[-1][1]
        from ink_knowledge.store import read
        with patch('ink_knowledge.store.read',wraps=read) as reads:
            self.assertEqual(self.store.observations(obs['program'],[selected['plan']],obs['target'],obs['workload'],limit=1),[selected])
            self.assertEqual(reads.call_count,1)
        wanted=[records[0][1]['plan'],selected['plan']]
        self.assertEqual(self.store.observations(obs['program'],wanted,obs['target'],obs['workload'],limit=2),[records[0][1],selected])
        self.assertEqual(self.store.observations(obs['program'],wanted,obs['target'],obs['workload'],limit=1),[records[0][1]])
        with closing(sqlite3.connect(self.root/'index.sqlite')) as db,db:
            plan=db.execute('EXPLAIN QUERY PLAN SELECT id FROM observations WHERE program_id=? AND plan_id=? AND target=? AND workload=? ORDER BY id LIMIT 1',
                            (obs['program'],selected['plan'],canonical(obs['target']).decode(),canonical(obs['workload']).decode())).fetchall()
            self.assertTrue(any('COVERING INDEX observation_lookup' in row[3] for row in plan),plan)
            # Previously built disposable indexes work with the new query too.
            db.execute('DROP INDEX observation_lookup')
            db.execute('CREATE INDEX observation_lookup ON observations(program_id,plan_id,target,workload)')
        self.assertEqual(self.store.observations(obs['program'],[selected['plan']],obs['target'],obs['workload'],limit=1),[selected])
        self.store.rebuild()
        self.assertEqual(self.store.observations(obs['program'],[selected['plan']],obs['target'],obs['workload'],limit=1),[selected])
    def test_cost_lookup_empty_budget_and_forged_index_never_supply_evidence(self):
        with patch.object(self.store,'rebuild') as rebuild:
            self.assertEqual(self.store.observations('1'*64,[],{},{}),[])
            self.assertEqual(self.store.observations('1'*64,['2'*64],{}, {},limit=0),[])
            rebuild.assert_not_called()
        with self.assertRaises(ValueError):self.store.observations('1'*64,[identity({'plan':i}) for i in range(1025)],{}, {})
        obs=dict(schema=1,program='1'*64,entries=[identity(self.a)],plan='2'*64,
                 target=dict(hardware='test',driver='test',toolchain='test',backend='cpu',bridge='host'),
                 workload=dict(shape=[48],distribution='test',concurrency=1,residency='host'),
                 metrics=dict(complete_call_ns=['100'],peak_bytes=None))
        self.store.rebuild();oid=self.store.observe(obs)
        with closing(sqlite3.connect(self.root/'index.sqlite')) as db,db:
            db.execute('UPDATE observations SET plan_id=? WHERE id=?',('3'*64,oid))
        self.assertEqual(self.store.observations('1'*64,['3'*64],obs['target'],obs['workload']),[])
        (self.root/'store/observations'/f'{oid}.json').write_text(json.dumps({**obs,'plan':'3'*64}))
        with self.assertRaisesRegex(ValueError,'hash mismatch'):
            self.store.observations('1'*64,['3'*64],obs['target'],obs['workload'])
if __name__=='__main__':unittest.main()
