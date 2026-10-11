"""Proof acceptance requires the independently built Ink checker.

Set INK_COMPILER to select a binary; otherwise the pinned parent checkout's
target/release/ink is used. No mock can establish semantic correctness.
"""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.performance_laws import named_laws, publish

KNOWLEDGE = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', KNOWLEDGE.parent / 'target/release/ink'))
SOURCE = '''module performance_laws;
fn repeat_subtract(x:u32,k:u32)->u32{return repeat(4096,x,fn(i)=>fn(a)=>a-k);}
fn repeat_product(x:u32,k:u32)->u32{return repeat(4096,x,fn(i)=>fn(a)=>a+k*k);}
fn repeat_identity(x:u32)->u32{return repeat(4096,x,fn(i)=>fn(a)=>a);}
fn repeat_cancel(x:u32,k:u32)->u32{return repeat(4096,x,fn(i)=>fn(a)=>a+k-k);}
fn scaled_sum(xs:List<u32>,k:u32)->u32{return sum(xs.map(fn(x)=>x*k));}
fn zero_sum(xs:List<u32>)->u32{return sum(xs.map(fn(x)=>0));}
fn mapped_count(xs:List<u32>)->u64{return count(xs.map(fn(x)=>x*x+7));}
fn true_filter_sum(xs:List<u32>)->u32{return sum(xs.filter(fn(x)=>true));}
fn false_filter_count(xs:List<u32>)->u64{return count(xs.filter(fn(x)=>false));}
fn filter_idempotent(xs:List<u32>)->List<u32>{return xs.filter(fn(x)=>x<7).filter(fn(x)=>x<7);}
fn filter_fusion(xs:List<u32>)->List<u32>{return xs.filter(fn(x)=>x<7).filter(fn(x)=>x>2);}
'''


class PerformanceLawTests(unittest.TestCase):
    def test_deterministic_canonical_objects_and_discovery(self):
        first = [(n, identity(semantic_entry(l))) for n, l in named_laws()]
        self.assertEqual(first, [(n, identity(semantic_entry(l))) for n, l in named_laws()])
        self.assertEqual(len(first), len({i for _, i in first}))
        with tempfile.TemporaryDirectory() as temp:
            store, manifest = publish(Path(temp))
            repeat_ids = store.query(kind='rewrite', operation='call:repeat', result={'Value': 'U32'})
            self.assertEqual(len(repeat_ids), 4)
            self.assertEqual(len(store.bundle(list(manifest['names'].values()))['objects']), len(first))

    @unittest.skipUnless(COMPILER.is_file(), 'build target/release/ink or set INK_COMPILER')
    def test_real_checker_accepts_induction_and_planner_applications(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            store, manifest = publish(root / 'knowledge')
            source, core, selected = root / 'source.ink', root / 'core.json', root / 'selection.json'
            source.write_text(SOURCE)
            subprocess.run([COMPILER, 'emit-core', source, '-o', core], check=True, capture_output=True)
            result = subprocess.run([COMPILER, 'knowledge-check', core, store.root / 'view.json'],
                                    check=True, capture_output=True, text=True)
            self.assertEqual(len(json.loads(result.stdout)['entries']), len(named_laws()))
            planner = KNOWLEDGE.parent / 'planner/plan.py'
            subprocess.run([sys.executable, planner, '--compiler', COMPILER, '--core', core,
                            '--snapshot', store.data / 'snapshot.json', '--budget', '4096', '-o', selected],
                           check=True, capture_output=True)
            package = json.loads(selected.read_text())
            expected = {manifest['names'][n] for n in (
                'repeat_subtract_u32', 'repeat_product_u32', 'repeat_identity_u32', 'repeat_cancel_u32',
                'scaled_sum_u32', 'zero_sum_u32', 'mapped_count_u32', 'true_filter_u32',
                'false_filter_count_u32', 'filter_idempotent_u32', 'filter_fusion_u32')}
            selected_ids = {s['law'] for s in package['applications']}
            missing = [n for n, i in manifest['names'].items() if i in expected - selected_ids]
            self.assertFalse(missing, missing)
            subprocess.run([COMPILER, 'check-selection', core, selected], check=True, capture_output=True)

    @unittest.skipUnless(COMPILER.is_file(), 'build target/release/ink or set INK_COMPILER')
    def test_hash_valid_forged_result_and_missing_induction_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source, core = root / 'source.ink', root / 'core.json'
            source.write_text(SOURCE)
            subprocess.run([COMPILER, 'emit-core', source, '-o', core], check=True, capture_output=True)
            laws = dict(named_laws())
            forged = copy.deepcopy(laws['zero_sum_u32'])
            forged['to']['node']['Word'] = 1
            missing_induction = copy.deepcopy(laws['repeat_subtract_u32'])
            missing_induction['proof'] = 'Normalize'
            for name, candidate in [('wrong-result', forged), ('missing-induction', missing_induction)]:
                obj = semantic_entry(candidate)
                store = Store.publish(root / name, [obj])
                view = store.root / 'view.json'
                view.write_bytes(canonical(store.bundle([identity(obj)])) + b'\n')
                rejected = subprocess.run([COMPILER, 'knowledge-check', core, view],
                                          capture_output=True, text=True)
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
                self.assertIn('semantic normal forms differ', rejected.stderr)
                self.assertNotIn('identity mismatch', rejected.stderr)


if __name__ == '__main__':
    unittest.main()
