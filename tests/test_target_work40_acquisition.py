"""Native emitted work must be observed or explicitly unavailable, never guessed."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
PARSER = ROOT / 'tools/js-instrumentation/node_modules/acorn/dist/acorn.mjs'


class Acquisition(unittest.TestCase):
    def observe(self, source, args, expected):
        parser = Path(os.environ.get('INK_ACORN_PARSER', PARSER))
        self.assertTrue(parser.is_file(), 'npm ci --prefix knowledge/tools/js-instrumentation')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original, instrumented, receipt = [root / name for name in ('original.mjs', 'instrumented.mjs', 'receipt.json')]
            original.write_text(source)
            script = os.environ.get('INK_TARGET_WORK_INSTRUMENTER', str(ROOT / 'producers/target_work40_js.mjs'))
            run = subprocess.run(['node', script, str(original), str(instrumented), str(receipt), str(parser)], capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            driver = root / 'driver.mjs'
            driver.write_text('''import fs from 'node:fs';import assert from 'node:assert/strict';
import * as original from './original.mjs';import * as changed from './instrumented.mjs';
const [args,expected]=JSON.parse(process.argv[2]),r=JSON.parse(fs.readFileSync(new URL('./receipt.json',import.meta.url)));
const left=structuredClone(args),right=structuredClone(args);
changed[r.prefix+'_reset']();const a=await original.call('entry',left),b=await changed.call('entry',right);
assert.deepEqual(b,a);assert.deepEqual(b,expected);assert.deepEqual(right,left);
console.log(JSON.stringify({receipt:r,observation:changed[r.prefix+'_snapshot']()}));
''')
            run = subprocess.run(['node', str(driver), json.dumps([args, expected])], capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            return json.loads(run.stdout)

    def count(self, result, *kinds):
        counts = result['observation']['sites']
        return sum((counts[s['id']] or 0) if s['id'] < len(counts) else 0 for s in result['receipt']['sites'] if s['kind'] in kinds)

    def test_chained_native_factory_and_comparator_are_observed(self):
        result = self.observe('export function call(_, [xs]){return Array.from(xs).sort((a,b)=>a-b)}', [[3, 1, 2]], [1, 2, 3])
        self.assertEqual(self.count(result, 'copy_or_allocation_call'), 1)
        self.assertGreater(self.count(result, 'native_callback_iterations'), 0)
        self.assertTrue(any('loop_iterations' in row['components'] for row in result['observation']['unknown']))

    def test_default_typed_sort_has_unknown_native_traversal_and_no_new_array(self):
        source = 'export function call(_, [xs]){const out=Uint32Array.from(xs);out.sort();return Array.from(out)}'
        result = self.observe(source, [[3, 1, 2]], [1, 2, 3])
        self.assertEqual(self.count(result, 'copy_or_allocation_call'), 2)
        unknown = result['observation']['unknown']
        sort_site = next(s['id'] for s in result['receipt']['sites'] if s['kind']=='copy_or_allocation_call' and s['start']==source.index('out.sort()'))
        self.assertTrue(any(row['site']==sort_site and 'loop_iterations' in row['components'] for row in unknown))

    def test_reduce_and_short_circuit_callbacks_count_actual_visits(self):
        result = self.observe('export function call(_, [xs]){const sum=xs.reduce((a,b)=>a+b,0);const found=xs.some(x=>x===2);return sum+(found?10:0)}', [[1, 2, 3]], 16)
        self.assertEqual(self.count(result, 'native_callback_iterations'), 5)
        self.assertEqual(self.count(result, 'copy_or_allocation_call'), 0)

    def test_factories_with_mapping_and_exact_typed_copy(self):
        result = self.observe('export function call(_, [xs]){const a=Uint32Array.from(xs,x=>x+1);const b=Uint32Array.from(a);return b.reduce((x,y)=>x+y,0)}', [[1, 2, 3]], 9)
        self.assertEqual(result['observation']['copy_bytes'], 12)
        self.assertEqual(self.count(result, 'native_callback_iterations'), 6)
        self.assertEqual(self.count(result, 'copy_or_allocation_call'), 2)

    def test_equal_width_numeric_conversion_is_not_a_known_plain_byte_copy(self):
        result = self.observe('export function call(_, [xs]){const a=Float32Array.from(xs);const b=new Uint32Array(3);b.set(a);return b[0]+b[1]+b[2]}', [[1, 2, 3]], 6)
        self.assertEqual(result['observation']['copy_bytes'], 0)
        self.assertTrue(any(row['reason']=='set byte extent or conversion unknown' for row in result['observation']['unknown']))

    def test_receiver_getter_arguments_and_lexical_await_keep_order(self):
        source = '''export async function call(){let order='';const receiver={get slice(){order+='get;';return function(x){order+='call;';return this===receiver?x:99}}};
function object(){order+='receiver;';return receiver}async function arg(){order+='arg;';return 7}
const value=object().slice(await arg());return [order,value]}'''
        result = self.observe(source, [], ['receiver;get;arg;call;', 7])
        self.assertTrue(any('implementation/carrier unknown' in row['reason'] for row in result['observation']['unknown']))

    def test_nested_calls_literals_and_loop_bodies_keep_all_sites(self):
        source = 'export function call(_, [xs]){let total=0;for(const x of xs)total+=Array.from([x],v=>v+1).reduce((a,b)=>a+b,0);return total}'
        result = self.observe(source, [[1, 2, 3]], 9)
        self.assertEqual(self.count(result, 'loop_iterations'), 3)
        self.assertEqual(self.count(result, 'native_callback_iterations'), 6)
        self.assertEqual(self.count(result, 'allocation_events'), 3)
        self.assertEqual(self.count(result, 'copy_or_allocation_call'), 3)

    def test_parentheses_spread_and_destructuring_keep_receiver_and_arguments(self):
        source = "export function call(_, [xs],{offset=1}={}){return ((xs)).slice(...[offset]).map(x=>({x})).map(({x=7})=>x)}"
        result = self.observe(source, [[1, 2, 3]], [2, 3])
        self.assertEqual(self.count(result, 'native_callback_iterations'), 4)
        self.assertEqual(self.count(result, 'copy_or_allocation_call'), 3)

    def test_unexecuted_callback_calls_do_not_acquire_runtime_events(self):
        result = self.observe('export function call(_, [xs]){return false?Array.from(xs).sort((a,b)=>a-b):7}', [[3, 2, 1]], 7)
        self.assertEqual(self.count(result, 'native_callback_iterations','copy_or_allocation_call'), 0)
        self.assertEqual(result['observation']['unknown'], [])

    def test_sparse_visits_and_callback_this_are_preserved(self):
        source = '''export function call(){const xs=new Array(3);xs[2]=7;let visits=0;
const mapped=xs.map(function(x){visits++;return x+this.add},{add:2});
const dense=Array.from(xs,x=>x??0);return [visits,0 in mapped,mapped[2],dense[0]]}'''
        result = self.observe(source, [], [1, False, 9, 0])
        self.assertEqual(self.count(result, 'native_callback_iterations'), 4)


class Sidecar(unittest.TestCase):
    def inputs(self, root):
        from producers import target_work40_sidecar as sidecar
        paths={name:root/name for name in ('trace','instrumenter','runner')}
        for name,path in paths.items():path.write_text(name)
        trace={'status':'untimed-complete-output-replayed','scope':'test','rows':[{'boundary':'owned','entry':'entry','id':'fixture','components':{},'known':{},'unknown':[]}]}
        paths['trace'].write_text(json.dumps(trace))
        return sidecar, paths, {'boundary':'owned','host':{'engine':'test'}}

    def test_acquisition_fingerprint_is_added_without_mutating_caller(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);sidecar,paths,cohort=self.inputs(root)
            rows=sidecar.produce(root/'out',paths,cohort);data=json.loads(Path(rows[0]['path']).read_text())
            self.assertNotIn('acquisition',cohort)
            self.assertEqual(data['cohort']['acquisition'],{name:sidecar.sha(paths[name]) for name in ('instrumenter','runner')})

    def test_trace_hash_and_rows_come_from_same_snapshot(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);sidecar,paths,cohort=self.inputs(root);digest=sidecar.sha(paths['trace']);original_sha=sidecar.sha
            def mutate(path):
                paths['trace'].write_text('{}')
                return original_sha(path)
            with patch.object(sidecar,'sha',side_effect=mutate):rows=sidecar.produce(root/'out',paths,cohort)
            data=json.loads(Path(rows[0]['path']).read_text())
            self.assertEqual(data['bindings']['trace']['sha256'],digest)
            self.assertEqual(data['fixture_id'],'fixture')

    def test_trace_shape_and_row_limits_fail_before_publication(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);sidecar,paths,cohort=self.inputs(root)
            for trace in [[],{'status':'untimed-complete-output-replayed','rows':[{}]*4097}]:
                paths['trace'].write_text(json.dumps(trace))
                with self.assertRaises(ValueError):sidecar.produce(root/'out',paths,cohort)
                self.assertFalse((root/'out').exists())


if __name__ == '__main__':
    unittest.main()
