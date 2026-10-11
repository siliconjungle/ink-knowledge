"""Real checker/planner evidence for untrusted web integer proof objects."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.web_numeric_laws import named_laws, publish

KNOWLEDGE = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', KNOWLEDGE.parent / 'target/release/ink'))
SOURCE = '''module WebNumeric;
fn quadratic(xs:List<u32>,k:u32)->List<u32>{return xs.map(fn(x)=>repeat(4096,x,fn(i)=>fn(a)=>(a+k)*(a+k)-a*a-2*a*k+a));}
fn cubic(xs:List<u32>,k:u32)->List<u32>{return xs.map(fn(x)=>repeat(1024,x,fn(i)=>fn(a)=>(a+k)*(a+k)*(a+k)-a*a*a-3*a*a*k-3*a*k*k+a));}
fn bilinear(xs:List<u32>,k:u32)->List<u32>{return xs.map(fn(x)=>repeat(4096,x,fn(i)=>fn(a)=>(a+k)*(a-k)-a*a+a));}
fn partition(xs:List<u32>,k:u32)->List<u32>{return xs.map(fn(x)=>repeat(4096,x,fn(i)=>fn(a)=>a*k+a*(1-k)));}
fn quadratic_invariant(xs:List<u32>,k:u32)->List<u32>{return xs.map(fn(x)=>repeat(4096,x,fn(i)=>fn(a)=>(a+k)*(a+k)-a*a-2*a*k+a-k*k));}
fn cubic_invariant(xs:List<u32>,k:u32)->List<u32>{return xs.map(fn(x)=>repeat(1024,x,fn(i)=>fn(a)=>(a+k)*(a+k)*(a+k)-a*a*a-3*a*a*k-3*a*k*k+a-k*k*k));}
fn map_quadratic(xs:List<u32>,k:u32)->List<u32>{return xs.map(fn(x)=>(x+k)*(x+k)-x*x-2*x*k);}
fn map_cubic(xs:List<u32>,k:u32)->List<u32>{return xs.map(fn(x)=>(x+k)*(x+k)*(x+k)-x*x*x-3*x*x*k-3*x*k*k);}
'''


def run(*args):
    return subprocess.run([str(arg) for arg in args], check=True, capture_output=True, text=True)


class WebNumericLawTests(unittest.TestCase):
    def test_deterministic_and_new_canonical_sources(self):
        laws = named_laws()
        self.assertEqual(len(laws), 24)
        ids = [identity(semantic_entry(candidate)) for _, candidate in laws]
        self.assertEqual(ids, [identity(semantic_entry(candidate)) for _, candidate in named_laws()])
        self.assertEqual(len(ids), len(set(ids)))
        existing = []
        for path in (KNOWLEDGE / 'store/objects').glob('*.json'):
            obj = json.loads(path.read_text())
            if obj['kind'] == 'rewrite' and path.stem not in set(ids):
                existing.append(obj['payload'])
        self.assertTrue(existing)
        existing_sources = {canonical(candidate['from']) for candidate in existing}
        for name, candidate in laws:
            self.assertNotIn(canonical(candidate['from']), existing_sources, name)
            self.assertNotIn('F32', json.dumps(candidate))
        with tempfile.TemporaryDirectory() as temp:
            store, manifest = publish(Path(temp))
            self.assertEqual(len(store.query(kind='rewrite', operation='call:repeat')), 18)
            self.assertEqual(len(manifest['names']), 24)

    @unittest.skipUnless(COMPILER.is_file(), 'build release compiler or set INK_COMPILER')
    def test_real_checker_accepts_all_and_planner_replays_u32_applications(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            store, manifest = publish(root / 'knowledge')
            source, core, selected = root / 'source.ink', root / 'core.json', root / 'selection.json'
            source.write_text(SOURCE)
            run(COMPILER, 'emit-core', source, '-o', core)
            accepted = json.loads(run(COMPILER, 'knowledge-check', core, store.root / 'view.json').stdout)
            self.assertEqual(len(accepted['entries']), 24)
            run(sys.executable, KNOWLEDGE.parent / 'planner/plan.py', '--compiler', COMPILER,
                '--core', core, '--snapshot', store.data / 'snapshot.json', '--budget', 4096, '-o', selected)
            package = json.loads(selected.read_text())
            expected = {identifier for name, identifier in manifest['names'].items() if name.endswith('_u32')}
            self.assertEqual({app['law'] for app in package['applications']}, expected)
            run(COMPILER, 'check-selection', core, selected)

    @unittest.skipUnless(COMPILER.is_file(), 'build release compiler or set INK_COMPILER')
    def test_hash_valid_wrong_closed_form_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source, core = root / 'source.ink', root / 'core.json'
            source.write_text(SOURCE)
            run(COMPILER, 'emit-core', source, '-o', core)
            forged = copy.deepcopy(dict(named_laws())['repeat_cubic_increment_u32'])
            forged['to'] = forged['from']['node']['Op'][1][1]  # wrongly drop nonzero increment
            obj = semantic_entry(forged)
            store = Store.publish(root / 'forged', [obj])
            view = store.root / 'view.json'
            view.write_bytes(canonical(store.bundle([identity(obj)])) + b'\n')
            result = subprocess.run([COMPILER, 'knowledge-check', core, view], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('semantic normal forms differ', result.stderr)
            self.assertNotIn('identity mismatch', result.stderr)


if __name__ == '__main__':
    unittest.main()
