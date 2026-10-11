"""Concat equations are untrusted data and must replay as actual source."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.web_sequence_laws import named_laws, publish
from producers.select_sequence_laws import select

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent / 'target/release/ink')).resolve()


def subject():
    functions, mappings = ['module SequenceProofs;'], []
    for name, _ in named_laws():
        t = name.rsplit('_', 1)[1]
        t = 'Bool' if t == 'bool' else t
        ls = 'List<' + t + '>'
        if name.startswith('concat_associative_'):
            body, result = 'xs.concat(ys).concat(zs)', ls
        elif name.startswith('concat_empty_left_'):
            body, result = 'ys.filter(fn(x)=>false).concat(xs)', ls
        elif name.startswith('concat_empty_right_'):
            body, result = 'xs.concat(ys.filter(fn(x)=>false))', ls
        elif name.startswith('concat_count_'):
            body, result = 'count(xs.concat(ys))', 'u64'
        elif name.startswith('concat_sum_'):
            body, result = 'sum(xs.concat(ys))', t
        elif name.startswith('concat_map_fusion_'):
            step = 'x&&x' if t == 'Bool' else 'x+x'
            body, result = f'xs.map(fn(x)=>{step}).concat(ys.map(fn(x)=>{step}))', ls
        elif name.startswith('concat_ordered_fold_'):
            body, result = 'foldr(xs.concat(ys),z,fn(x)=>fn(a)=>x-a)', t
        else:
            raise ValueError(name)
        functions.append(f'pub fn {name}(xs:{ls},ys:{ls},zs:{ls},z:{t})->{result}{{return {body};}}')
        mappings.append((name, name))
    return '\n'.join(functions) + '\n', mappings


@unittest.skipUnless(COMPILER.is_file(), 'new concat compiler required')
class SequenceLawTests(unittest.TestCase):
    def test_all_equations_admit_and_replay_from_typed_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            store, manifest = publish(root / 'knowledge')
            text, mappings = subject()
            ink, core = root / 'source.ink', root / 'source.core.json'
            ink.write_text(text)
            subprocess.run([COMPILER, 'emit-core', ink, '-o', core], check=True, capture_output=True)
            admission = subprocess.run([COMPILER, 'knowledge-check', core, store.root / 'view.json'],
                                       check=True, capture_output=True, text=True)
            self.assertEqual(len(json.loads(admission.stdout)['entries']), 32)
            receipt = select(COMPILER, core, store.root, mappings, root / 'selection.json')
            self.assertEqual(set(receipt['applied_laws']), set(manifest['names'].values()))
            self.assertEqual(len(set(manifest['names'].values())), 32)
            self.assertTrue(all('concat_sum_f32' != name for name in manifest['names']))
            # Reification, not just term equality, must succeed for curried folds.
            subprocess.run([COMPILER, 'emit-core', ink, '--selection', root / 'selection.json',
                            '-o', root / 'selected.core.json'], check=True, capture_output=True)

    def test_valid_hash_commutative_concat_forgery_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            ink, core = root / 'source.ink', root / 'source.core.json'
            ink.write_text(subject()[0])
            subprocess.run([COMPILER, 'emit-core', ink, '-o', core], check=True, capture_output=True)
            forged = copy.deepcopy(dict(named_laws())['concat_associative_u32'])
            # Concat is ordered, so exchange of xs and ys is not a law.
            inner = forged['to']['node']['Op'][1][1]
            first = forged['to']['node']['Op'][1][0]
            forged['to']['node']['Op'][1][0] = inner['node']['Op'][1][0]
            inner['node']['Op'][1][0] = first
            obj = semantic_entry(forged)
            store = Store.publish(root / 'forged', [obj])
            store.rebuild()
            view = store.root / 'view.json'
            view.write_bytes(canonical(store.bundle([identity(obj)])) + b'\n')
            rejected = subprocess.run([COMPILER, 'knowledge-check', core, view], capture_output=True, text=True)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('semantic normal forms differ', rejected.stderr)
            self.assertNotIn('identity mismatch', rejected.stderr)


if __name__ == '__main__':
    unittest.main()
