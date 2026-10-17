from contextlib import closing
import copy,json,sqlite3,tempfile,unittest
from unittest.mock import patch
from pathlib import Path
from ink_knowledge import Store,entry,identity,canonical
from ink_knowledge.store import MAX_VIEW_ENTRIES
class StoreTests(unittest.TestCase):
    def test_selective_queries_preserve_combined_filters_paging_and_snapshot_membership(self):
        objects=[entry('definition','query-v1',{'node':{'Op':['call:rare' if i%13==0 else 'call:common',[]]},'i':i},
                       parameters={'x':'U32','y':'U32' if i%3==0 else 'Bool'},result='U32',
                       effects=['read'] if i%5==0 else [],conditions=[{'from':1,'to':1}] if i%7==0 else []) for i in range(100)]
        store=Store.publish(self.root/'filters',objects)
        store.rebuild()
        historical=Store(store.root,store.data/'snapshots'/f'{store.snapshot_id}.json')
        store.extend([entry('definition','query-v1',{'node':{'Op':['call:rare',[]]},'i':101},parameters={'x':'U32'})]).ensure_index()
        for filters in [dict(operation='call:rare'),dict(operation='call:common',effect='read'),
                        dict(parameter_type='U32'),dict(parameter_type='Bool',condition={'from':1,'to':1}),
                        dict(operation='missing'),dict(operation='call:rare',kind='theorem')]:
            def matches(obj):
                iface=obj['interface']
                available={'operation':iface['operations'],'effect':iface['effects'],
                           'parameter_type':iface['parameters'].values(),'condition':iface['conditions'],'kind':[obj['kind']]}
                return all(value in available[name] for name,value in filters.items())
            expected=sorted(identity(obj) for obj in objects if matches(obj))
            actual=[];after=None
            while True:
                page=historical.query(**filters,after=after,limit=3)
                actual.extend(page)
                if len(page)<3:break
                after=page[-1]
            self.assertEqual(actual,expected)
            self.assertEqual(historical.query(**filters,limit=0),[])

    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        self.a=entry('definition','test-v1',dict(body='a'),parameters={'x':'U32'},result='U32')
        self.b=entry('theorem','test-v1',dict(body='b'),[identity(self.a)],conditions=[{'from':1,'to':1}])
        self.store=Store.publish(self.root,[self.a,self.b],{'a':identity(self.a)})
    def tearDown(self):self.temp.cleanup()
    def test_candidate_packages_roundtrip_above_the_individual_proof_entry_limit(self):
        with patch('ink_knowledge.store.MAX_ENTRY_BYTES',1024), patch('ink_knowledge.store.MAX_VIEW_BYTES',4096):
            candidate=entry('implementation','ink-implementation-candidate-v1',dict(request={'package':'x'*1200}))
            key=identity(candidate)
            store=Store.publish(self.root/'large-candidate',[candidate],{'candidate':key})
            self.assertEqual(Store(store.root).object(key),candidate)
            with self.assertRaisesRegex(ValueError,'knowledge object byte limit'):
                entry('definition','test-v1',dict(body='x'*1200))

    def test_compact_leaf_packing_keeps_exact_authenticated_pins(self):
        objects=[entry('definition','test-v1',dict(body=i)) for i in range(71)]
        for size in [1,2,8,64]:
            store=Store.publish(self.root/str(size),objects,leaf_size=size)
            expected={identity(x) for x in objects}
            self.assertEqual(set(store.members()),expected)
            self.assertTrue(all(len(w['entries'])<=size for w in store.members().values()))
            store.rebuild();view=Store(store.root).bundle(sorted(expected))
            self.assertEqual(set(view['objects']),expected)
            for i,w in view['membership'].items():
                node=identity(dict(schema=1,entries=w['entries']))
                self.assertIn(i,w['entries'])
                for step in w['path']:
                    left,right=(step['sibling'],node) if step['left'] else (node,step['sibling'])
                    node=identity(dict(schema=1,left=left,right=right))
                self.assertEqual(node,view['snapshot']['root'])
        for size in [0,65,True]:
            with self.assertRaises(ValueError):Store.publish(self.root/'bad',objects,leaf_size=size)
    def test_active_and_prior_readers_survive_a_stale_disposable_index(self):
        self.store.rebuild();prior=Store(self.root)
        c=entry('definition','test-v1',dict(body='new'))
        next_store=Store.publish(self.root,[self.a,self.b,c],{'c':identity(c)})
        current=Store(self.root)
        self.assertEqual(set(current.bundle([identity(c)])['objects']),{identity(c)})
        self.assertIn(identity(c),current.query(kind='definition'))
        next_store.rebuild()
        self.assertEqual(set(prior.bundle([identity(self.b)])['objects']),{identity(self.a),identity(self.b)})
        self.assertNotIn(identity(c),prior.query(kind='definition'))

    def test_reverse_dependency_index_migrates_atomically_without_changing_exports(self):
        self.store.rebuild();original=Store(self.root).bundle([identity(self.b)])
        with closing(sqlite3.connect(self.root/'index.sqlite'))as db,db:
            db.execute('DROP INDEX dependency_parent_lookup');db.execute('DROP INDEX membership_entry_lookup')
        store=Store(self.root);self.assertTrue(store.ensure_index());self.assertFalse(store.ensure_index())
        self.assertEqual(canonical(Store(self.root).bundle([identity(self.b)])),canonical(original))
        with closing(sqlite3.connect(self.root/'index.sqlite'))as db:
            plan=list(db.execute('EXPLAIN QUERY PLAN SELECT entry_id FROM dependencies WHERE dependency_id=?',(identity(self.a),)))
            self.assertTrue(any('dependency_parent_lookup'in row[3]for row in plan))
            self.assertEqual(list(db.execute('PRAGMA foreign_key_check')),[])

    def test_frequently_used_pinned_snapshot_survives_publication_churn(self):
        from ink_knowledge.index_cache import MAX_SNAPSHOTS
        self.store.rebuild();pin=self.store.data/'snapshots'/f'{self.store.snapshot_id}.json'
        original=canonical(self.store.bundle([identity(self.b)]))
        active=self.store
        for i in range(MAX_SNAPSHOTS+3):
            active=active.extend([entry('definition','test-v1',dict(body=i))])
            active.ensure_index()
            self.assertFalse(Store(self.root,pin).ensure_index())
        self.assertEqual(canonical(Store(self.root,pin).bundle([identity(self.b)])),original)
        with closing(sqlite3.connect(self.root/'index.sqlite')) as db:
            self.assertLessEqual(db.execute('SELECT count(*) FROM snapshots').fetchone()[0],MAX_SNAPSHOTS)

    def test_recency_hint_never_creates_a_missing_disposable_index(self):
        from ink_knowledge.index_cache import touch
        path=self.root/'absent.sqlite'
        touch(path,self.store.snapshot_id)
        self.assertFalse(path.exists())

    def test_single_canonical_read_preserves_validation_and_noncanonical_json(self):
        key=identity(self.a);path=self.root/'store/objects'/f'{key}.json'
        # Content identities describe canonical JSON, not whitespace/key order.
        path.write_text(json.dumps(self.a,indent=2,sort_keys=False))
        self.assertEqual(Store(self.root).object(key),self.a)
        for bad in [dict(self.a,schema=True),dict(self.a,payload={'bad':1.5}),
                    dict(self.a,payload={'bad':1<<65}),dict(self.a,dependencies=['x'])]:
            path.write_text(json.dumps(bad))
            with self.assertRaises(ValueError):Store(self.root).object(key)
        path.write_text(json.dumps(self.a))
        with patch('ink_knowledge.store.MAX_ENTRY_BYTES',100):
            with self.assertRaisesRegex(ValueError,'byte limit'):Store(self.root).object(key)
        # Re-read on every export; a valid earlier receipt cannot mask tampering.
        self.assertEqual(Store(self.root).object(key),self.a)
        path.write_text(json.dumps(dict(self.a,semantics='forged')))
        with self.assertRaisesRegex(ValueError,'content mismatch'):Store(self.root).object(key)

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
        from ink_knowledge.store import _read_canonical
        with patch('ink_knowledge.store.sqlite3.connect',wraps=sqlite3.connect) as connects, \
             patch('ink_knowledge.store._read_canonical',wraps=_read_canonical) as reads, \
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
            db.execute('UPDATE witnesses SET witness=? WHERE id=(SELECT witness_id FROM members WHERE entry_id=?)',
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
            witness=db.execute('SELECT witness_id FROM members WHERE entry_id=?',(aid,)).fetchone()[0]
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
    def test_bundle_accepts_long_dags_preserves_object_limits_and_closes_failed_exports(self):
        objects=[]
        for number in range(66):
            objects.append(entry('definition','test-v1',dict(body=number),[identity(objects[-1])] if objects else []))
        store=Store.publish(self.root,objects);store.rebuild()
        self.assertEqual(len(Store(self.root).bundle([identity(objects[-2])])['objects']),65)
        self.assertEqual(len(Store(self.root).bundle([identity(objects[-1])])['objects']),66)
        # A failed read transaction must not retain a lock on the disposable index.
        with closing(sqlite3.connect(self.root/'index.sqlite',timeout=0)) as db,db:
            db.execute('DELETE FROM names')
        leaves=[entry('definition','test-v1',dict(body=['leaf',i])) for i in range(MAX_VIEW_ENTRIES)]
        parents=[entry('definition','test-v1',dict(body=['parent',i]),[identity(x) for x in leaves[i:i+128]]) for i in range(0,MAX_VIEW_ENTRIES,128)]
        root=entry('definition','test-v1',dict(body='root'),[identity(x) for x in parents])
        store=Store.publish(self.root,[*leaves,*parents,root]);store.rebuild()
        with self.assertRaisesRegex(ValueError,'dependency closure limit'):
            Store(self.root).bundle([identity(root)])
    def test_index_forgery_cannot_supply_membership_authority(self):
        self.store.rebuild()
        with closing(sqlite3.connect(self.root/'index.sqlite')) as db,db:
            db.execute('UPDATE witnesses SET witness=?',(json.dumps({'entries':['0'*64],'path':[]}),))
        with self.assertRaises(ValueError):Store(self.root).bundle([identity(self.a)])
    def test_tampered_content_and_missing_dependencies_are_rejected(self):
        i=identity(self.a);p=self.root/'store/objects'/f'{i}.json'
        p.write_text(json.dumps({**self.a,'semantics':'forged'}))
        with self.assertRaises(ValueError):Store(self.root).bundle([i])
        with self.assertRaises(ValueError):Store.publish(self.root,[self.b])
    def test_pinned_snapshot_survives_publication_and_stale_index_uses_canonical_pin(self):
        original=self.store.snapshot_id;self.store.rebuild()
        c=entry('definition','test-v1',dict(body='c'))
        newer=Store.publish(self.root,[self.a,self.b,c]);self.assertNotEqual(original,newer.snapshot_id)
        self.assertEqual(set(newer.query()),{identity(self.a),identity(self.b),identity(c)})
        old=Store(self.root,self.root/'store/snapshots'/f'{original}.json')
        self.assertEqual(old.query(kind='theorem'),[identity(self.b)])
        self.assertEqual(set(old.bundle([identity(self.b)])['objects']),{identity(self.a),identity(self.b)})
    def test_explicit_pin_uses_canonical_queries_without_changing_active_index(self):
        condition={'from':{'flag':True},'to':{'flag':True}}
        scalar={'Value':'U32'}
        chosen=entry('rewrite','test-v1',{'node':{'Op':['call:demo',[]]}},parameters={'x':scalar},result=scalar,effects=['read'],conditions=[condition])
        near=entry('rewrite','test-v1',{'node':{'Op':['call:demo',[]]}},parameters={'x':scalar},result=scalar,effects=['read'],conditions=[{'from':{'flag':1},'to':{'flag':1}}])
        old=Store.publish(self.root,[self.a,self.b,chosen,near]);old.rebuild()
        cases=[{},dict(kind='rewrite'),dict(semantics='test-v1'),dict(operation='call:demo'),dict(result=scalar),dict(effect='read'),dict(parameter_type=scalar),dict(condition=condition),dict(kind='rewrite',semantics='test-v1',operation='call:demo',result=scalar,effect='read',parameter_type=scalar,condition=condition),dict(limit=0),dict(limit=1)]
        cases += [dict(after=i,limit=1) for i in sorted(old.members())]
        expected=[old.query(**case) for case in cases]
        extra=entry('definition','test-v1',{'body':'newest'})
        current=Store.publish(self.root,[self.a,self.b,chosen,near,extra]);current.rebuild()
        index_before=(self.root/'index.sqlite').read_bytes()
        pinned=Store(self.root,self.root/'store/snapshots'/f'{old.snapshot_id}.json')
        self.assertEqual(pinned.object(identity(chosen)),chosen)
        self.assertEqual([pinned.query(**case) for case in cases],expected)
        self.assertEqual(set(pinned.bundle([identity(self.b)])['objects']),{identity(self.a),identity(self.b)})
        self.assertEqual((self.root/'index.sqlite').read_bytes(),index_before)
        self.assertEqual(Store(self.root).query(kind='definition'),sorted([identity(self.a),identity(extra)]))
        (self.root/'index.sqlite').unlink()
        self.assertEqual(Store(self.root,self.root/'store/snapshots'/f'{old.snapshot_id}.json').query(condition=condition),[identity(chosen)])
        self.assertFalse((self.root/'index.sqlite').exists())
        for limit in [-1,1025,0.5]:
            with self.assertRaises(ValueError):pinned.query(limit=limit)
        with self.assertRaises(ValueError):pinned.query(after='not-a-hash')

    def test_explicit_pin_cannot_accept_forged_objects_trees_or_report_files(self):
        old=self.store.snapshot_id
        new=Store.publish(self.root,[self.a,self.b,entry('definition','test-v1',{'body':'new'})]);new.rebuild()
        pin=self.root/'store/snapshots'/f'{old}.json'
        pinned=Store(self.root,pin)
        forged={**self.a,'semantics':'forged'}
        object_path=self.root/'store/objects'/f'{identity(self.a)}.json'
        original=object_path.read_bytes();object_path.write_text(json.dumps(forged))
        with self.assertRaisesRegex(ValueError,'entry content mismatch'):pinned.object(identity(self.a))
        object_path.write_bytes(original)
        tree=self.root/'store/trees'/f'{pinned.snapshot["root"]}.json'
        tree.write_text(json.dumps({'schema':1,'entries':[]}))
        with self.assertRaises(ValueError):Store(self.root,pin).query()
        report=self.root/'report.json';report.write_text(json.dumps({'schema':1,'snapshot':old,'status':'pass'}))
        with self.assertRaises(ValueError):Store(self.root,report)

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
    def test_observation_limit_applies_only_to_requested_plans(self):
        self.store.rebuild()
        base=dict(schema=1,program='1'*64,entries=[],
                  target=dict(hardware='test',driver='test',toolchain='test',backend='cpu',bridge='host'),
                  workload=dict(shape=[100],distribution='zeros',concurrency=1,residency='host'),
                  metrics=dict(complete_call_ns=['100','200'],peak_bytes=0))
        observations=[dict(base,plan=c*64) for c in ('2','3')]
        observations.sort(key=identity)
        for obj in observations:self.store.observe(obj)
        wanted=observations[1]
        self.assertEqual(self.store.observations(base['program'],[wanted['plan']],base['target'],base['workload'],limit=1),[wanted])
        self.assertEqual(self.store.observations(base['program'],[],base['target'],base['workload'],limit=1),[])
        self.assertEqual(self.store.observations(base['program'],[wanted['plan']],base['target'],base['workload'],limit=0),[])
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
        from ink_knowledge.store import _read_canonical
        with patch('ink_knowledge.store._read_canonical',wraps=_read_canonical) as reads:
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
    def test_evidence_pages_cover_large_candidate_pools_and_all_repetitions(self):
        self.store.rebuild();program='1'*64
        target=dict(hardware='test',driver='test',toolchain='test',backend='cpu',bridge='host')
        workload=dict(shape=[48],distribution='test',concurrency=1,residency='host')
        plans=[identity({'plan':n})for n in range(1200)]
        expected=set()
        for n in range(2400):
            obs=dict(schema=1,program=program,entries=[],plan=plans[n%1200],target=target,workload=workload,
                metrics=dict(complete_call_ns=[str(n)],peak_bytes=100))
            expected.add(self.store.observe(obs))
        actual=list(self.store.iter_observations(program,plans,target,workload,page_size=37))
        self.assertEqual({identity(o)for o in actual},expected);self.assertEqual(len(actual),2400)
        # Filtering a forged disposable index row must not terminate paging.
        wanted=plans[:1];rows=self.store.observations(program,wanted,target,workload);rows.sort(key=identity)
        first=identity(rows[0])
        with closing(sqlite3.connect(self.root/'index.sqlite'))as db,db:
            db.execute('UPDATE observations SET plan_id=? WHERE id=?',(plans[1],first))
        actual=list(self.store.iter_observations(program,plans[1:2],target,workload,page_size=1))
        self.assertEqual(len(actual),2)
class CompactExtensions(unittest.TestCase):
 def test_large_compact_publication_preserves_witness_size_after_append(self):
  with tempfile.TemporaryDirectory() as tmp:
   objects=[entry('definition','test',{'number':i}) for i in range(70)]
   store=Store.publish(Path(tmp),objects,leaf_size=2)
   store=store.extend([entry('definition','test',{'number':70})])
   self.assertTrue(all(len(w['entries'])<=2 for w in store.members().values()))
   self.assertEqual(len(store.members()),71)
 def test_invalid_leaf_sizes_fail_closed(self):
  for size in [0,65,True]:
   with self.subTest(size=size),tempfile.TemporaryDirectory() as tmp:
    with self.assertRaisesRegex(ValueError,'leaf size'):Store.publish(Path(tmp),[],leaf_size=size)

if __name__=='__main__':unittest.main()
