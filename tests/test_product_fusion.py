"""Ordered traversal sharing is discovered, proved and emitted from source."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.product_fusion import specialize


class ProductFusion(unittest.TestCase):
    def test_source_records_captures_and_float_order(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        source = '''module product_discovery;
record Statistics { sum:u32, parity:Bool, mixed:u32, }
record FloatPair { first:f32, second:f32, }
fn statistics(xs:List<u32>,product_state_0:u32)->Statistics {
 return Statistics{
  sum:foldl(xs,0,fn(x,s)=>s+x+product_state_0),
  parity:foldl(xs,false,fn(x,s)=>s!=(x>product_state_0)),
  mixed:foldl(xs,17,fn(x,s)=>(s*3)^x)};
}
fn floating(xs:List<f32>,a:f32,b:f32)->FloatPair {
 return FloatPair{first:foldl(xs,a,fn(x,s)=>s+x),second:foldl(xs,b,fn(x,s)=>s*x)};
}
'''
        with tempfile.TemporaryDirectory() as temporary:
            d = Path(temporary)
            text = d / 'source.ink'
            text.write_text(source)

            def run(*args, **kwargs):
                result = subprocess.run(list(map(str, args)), capture_output=True, text=True,
                                        timeout=180, **kwargs)
                self.assertEqual(result.returncode, 0, result.stderr[-3000:])
                return result

            core, subject = d / 'core.json', d / 'subject.json'
            run(compiler, 'emit-core', text, '-o', core)
            run(compiler, 'emit-semantic', text, '-o', subject)
            checked = json.loads(core.read_text())
            meaning = json.loads(subject.read_text())
            proposals = specialize(meaning, checked)
            self.assertEqual(len(proposals), 2)
            for name, law in proposals:
                obj = semantic_entry(law)
                bank = Store.publish(d / ('proof-' + name), [obj])
                view = d / 'view.json'
                view.write_bytes(canonical(bank.bundle([identity(obj)])))
                run(compiler, 'knowledge-check', core, view)
                # Change only the emitted second lane to read the first lane.
                # The original proof cannot authorize coupled accumulators.
                if name.startswith('floating_'):
                    forged = copy.deepcopy(law)
                    def couple(value):
                        if isinstance(value, dict):
                            if value.get('Op', [None])[0] == 'field:second':
                                value['Op'][0] = 'field:first'
                            for child in value.values():
                                couple(child)
                        elif isinstance(value, list):
                            for child in value:
                                couple(child)
                    couple(forged['to'])
                    bad = semantic_entry(forged)
                    bank = Store.publish(d / 'forged', [bad])
                    view.write_bytes(canonical(bank.bundle([identity(bad)])))
                    result = subprocess.run([compiler, 'knowledge-check', core, view],
                                            capture_output=True, text=True, timeout=60)
                    self.assertNotEqual(result.returncode, 0)
            bank = Store.publish(d / 'knowledge', [])
            costs, selected = d / 'costs.json', d / 'selected.json'
            # This checks discovery and execution; synthetic prices are not a
            # claim that record allocation is profitable on a real target.
            costs.write_text(json.dumps(dict(schema=1, operation_costs={'call:foldl':1000})))
            env = dict(os.environ, PYTHONPATH=os.pathsep.join(map(str, [root/'knowledge', root/'planner'])))
            report = json.loads(run('python3', '-m', 'ink_planner.semantic_search',
                '--compiler', compiler, '--core', core, '--snapshot', bank.data/'snapshot.json',
                '--knowledge-root', bank.root, '--cost-model', costs, '--budget', '32',
                '--rounds', '4', '--time-seconds', '30', '-o', selected, env=env).stdout)
            self.assertTrue(any(x['module'] == 'producers.product_fusion' and x['candidates']
                                for x in report['database']['producers']))
            self.assertTrue(json.loads(selected.read_text())['applications'])
            run(compiler, 'check-selection', core, selected)
            run(compiler, 'build', core, '--core', '--target', 'javascript', '-o', d/'baseline.mjs')
            run(compiler, 'build', core, '--core', '--selection', selected,
                '--target', 'javascript', '-o', d/'selected.mjs')
            script = d/'verify.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import {functions as a} from './baseline.mjs';
import {functions as b} from './selected.mjs';
for(const seed of [0,1,0xffffffff]) for(const xs of [[],[1],[0xffffffff,3,5],Array.from({length:129},(_,i)=>(i*7919)>>>0)])
 assert.deepEqual(b.statistics(xs,seed),a.statistics(xs,seed));
for(const seed of [0,-0,1,Infinity,-Infinity,NaN]) for(const xs of [[],[0,-0],[1e20,-1e20,1],[Infinity,0],[-Infinity,NaN,1],[1.1,2.2,3.3]])
 assert.deepEqual(b.floating(xs,seed,seed),a.floating(xs,seed,seed));
''')
            run('node', script)

    def test_different_sequences_do_not_share_a_traversal(self):
        from producers.semantic_laws import value, var, op, lam, bound
        u = value('U32'); ls = value({'List':'U32'}); record = value({'Named':'Pair'})
        step = lam(u, lam(u, bound(u, 0)))
        fields = [op(u, 'call:foldl', var(ls, n), var(u, 'start'), step) for n in ['xs', 'ys']]
        subject = {'functions':{'test':op(record, 'record:Pair', *fields)}}
        core = {'program':{'records':{'Pair':[['left','U32'],['right','U32']]}}}
        self.assertEqual(specialize(subject, core), [])


if __name__ == '__main__':
    unittest.main()
