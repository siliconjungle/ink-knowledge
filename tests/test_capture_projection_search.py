"""Exercise catalogue discovery, independent admission and ordinary emission."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store


class CaptureProjectionSearch(unittest.TestCase):
    def test_normal_search_discovers_hoisting_and_preserves_wrapping_values(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            store = Store.publish(directory / 'knowledge', [])
            source = directory / 'source.ink'
            source.write_text('''module capture_search;
record Config{offset:u32,unused:List<u32>,}
fn total(xs:List<u32>,config:Config)->u32{
 return foldl(xs,0,fn(x)=>fn(acc)=>acc+x+config.offset);
}
''')
            def run(*arguments, **options):
                result = subprocess.run(list(map(str, arguments)), capture_output=True,
                                        text=True, timeout=120, **options)
                self.assertEqual(result.returncode, 0, result.stderr[-3000:])
                return result
            core = directory / 'core.json'
            run(compiler, 'emit-core', source, '-o', core)
            costs = directory / 'costs.json'
            costs.write_text(json.dumps(dict(schema=1, operation_costs={
                'estimate:loop_iterations': 128, 'estimate:let_binding': 0,
                'estimate:scalar': 1})))
            selection = directory / 'selection.json'
            environment = dict(os.environ, PYTHONPATH=os.pathsep.join(
                map(str, [root / 'knowledge', root / 'planner'])))
            report = json.loads(run('python3', '-m', 'ink_planner.semantic_search',
                '--compiler', compiler, '--core', core, '--snapshot',
                store.data / 'snapshot.json', '--knowledge-root', store.root,
                '--cost-model', costs, '--budget', '16', '--rounds', '4',
                '--time-seconds', '30', '--search-trace', directory / 'trace.json',
                '-o', selection, env=environment).stdout)
            producers = report['database']['producers']
            self.assertTrue(any(row['module'] == 'producers.capture_projections'
                                and row['candidates'] for row in producers))
            package = json.loads(selection.read_text())
            self.assertTrue(package['applications'])
            self.assertLess(report['selected_cost'], report['initial_cost'])
            self.assertEqual(json.loads((directory / 'trace.json').read_text())['snapshot'],
                             store.snapshot_id)
            run(compiler, 'check-selection', core, selection)
            emitted = directory / 'selected.mjs'
            run(compiler, 'build', core, '--core', '--selection', selection,
                '--target', 'javascript', '-o', emitted)
            script = directory / 'verify.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import {functions} from './selected.mjs';
for(const offset of [0,1,0xffffffff]){
 for(const xs of [[],[1],[0xffffffff,3,5]]){
  const expected=xs.reduce((acc,x)=>(acc+x+offset)>>>0,0);
  assert.equal(functions.total(xs,{offset,unused:[7,8]}),expected);
 }
}
''')
            run('node', script)
            self.assertEqual(Store(store.root).snapshot_id, store.snapshot_id)


if __name__ == '__main__':
    unittest.main()
