import json, tempfile, unittest
from pathlib import Path
from ink_knowledge.implementation_candidates import identity_selection, publish_candidates
from producers.aggregate_measurements import publish

class AggregateMeasurements(unittest.TestCase):
    def fixture(self, root, baseline_source='1'*64):
        package=identity_selection('1'*64)
        package['representation']='2'*64
        store,ids=publish_candidates(root/'db',[identity_selection(baseline_source),package],shared_knowledge=True)
        requests=root/'requests';requests.mkdir()
        (requests/'indexed.json').write_text(json.dumps(package))
        report=root/'report.json'
        report.write_text(json.dumps(dict(schema=4,instrumented=False,phases=[],measurements=[dict(candidate='indexed',rows=100,calls_per_sample=100,query='total_query',read_percent=90,samples=[dict(native_ns=7,ordinary_compiled_ink_ns=11)])])))
        target=dict(hardware='test',driver='test',toolchain='test',backend='rust',bridge='native')
        return store,report,requests,target,{'ordinary-source':ids[0],'indexed':ids[1]}

    def test_pairing_binds_candidates_and_preserves_missing_phases(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);store,report,requests,target,ids=self.fixture(root)
            manifest=publish([report],requests,target,store.root,candidate_ids=ids,compiler_sha256='3'*64)
            workload=dict(shape=dict(rows=100,calls=100),distribution=dict(workload=dict(query='total_query',read_percent=90,script='bench/point-delta/standalone-aggregate.rs.txt'),phase='action:batch_calls'),concurrency=1,residency='restored; acknowledgement after every call')
            from ink_knowledge import identity
            def measurement_id(candidate,compiler_sha256,emission_target):
                return identity(dict(schema=1,semantics="ink-implementation-measurement-v1",candidate=candidate,compiler_sha256=compiler_sha256,emission_target=emission_target))
            plans=[measurement_id(i,'3'*64,'rust') for i in ids.values()]
            observations=store.observations('1'*64,plans,target,workload)
            self.assertEqual(len(observations),2)
            self.assertEqual({tuple(o['metrics']['complete_call_ns']) for o in observations},{('7',),('11',)})
            self.assertEqual({tuple(o['entries']) for o in observations},{(i,) for i in ids.values()})
            self.assertTrue(all(o['metrics']['peak_bytes'] is None for o in observations))
            self.assertEqual(store.observations('1'*64,plans,target,{**workload,'distribution':{**workload['distribution'],'phase':'initialise'}}),[])
            self.assertEqual(manifest['snapshot'],store.snapshot_id)

    def test_rejects_cross_source_baseline_and_instrumented_timings(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);store,report,requests,target,ids=self.fixture(root,baseline_source='4'*64)
            with self.assertRaisesRegex(ValueError,'baseline/source'):
                publish([report],requests,target,store.root,candidate_ids=ids,compiler_sha256='3'*64)
            data=json.loads(report.read_text());data['instrumented']=True;report.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError,'uninstrumented'):
                publish([report],requests,target,store.root,candidate_ids=ids,compiler_sha256='3'*64)

if __name__=='__main__':unittest.main()
