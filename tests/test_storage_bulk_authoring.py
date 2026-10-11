import json,os,subprocess,tempfile,unittest
from pathlib import Path
from producers.point_delta import sub,match
from producers.action_replacement import var
class StorageBulkAuthoring(unittest.TestCase):
    def test_simultaneous_substitution_avoids_match_capture_and_shadowing(self):
        source=match(var('xs'),[(['tail'],{'Binary':dict(op='+',left=var('tail'),right=var('free'))})])
        actual=sub(source,{'free':var('tail'),'tail':var('outside')})
        branch=actual['Match']['branches'][0];binder=branch['bindings'][0]
        self.assertNotEqual(binder,'tail');self.assertEqual(branch['body']['Binary']['left'],var(binder));self.assertEqual(branch['body']['Binary']['right'],var('tail'))
        self.assertEqual(sub({'Binary':dict(op='+',left=var('a'),right=var('b'))},{'a':var('b'),'b':var('c')}),{'Binary':dict(op='+',left=var('b'),right=var('c'))})
    def test_boolean_identity_does_not_authorise_a_non_monoid_reducer(self):
        compiler=Path(os.environ.get('INK_COMPILER','../target/debug/ink')).resolve()
        if not compiler.exists():self.skipTest('INK_COMPILER is required')
        from producers.representations import generate
        with tempfile.TemporaryDirectory() as tmp:
            directory=Path(tmp);source=directory/'parity.ink';model=directory/'model.json'
            source.write_text('module parity; record Row{active:Bool,} state Rows:Table<u64,Row> = Table.empty(); fn parity(xs:List<Row>)->Bool{return foldr(xs,false,fn(row)=>fn(acc)=>row.active!=acc);} keep odd:Bool = parity(Rows.values()); query odd_query()->Bool reads(odd){return odd;}')
            r=subprocess.run([str(compiler),'emit-action-model',str(source),'-o',str(model)],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
            with self.assertRaises(ValueError):generate(json.loads(model.read_text()),directory/'proposal',cache_query='odd_query',preserve_cache=True,compact_queries=True,aggregate_query=True)
