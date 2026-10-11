"""Frozen-compiler admission, replay, novelty and old-catalogue controls."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.web_compute2_laws import named_laws, publish, representative_source

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent / 'toolchain/ink-sequence-proofs'))
BASELINE = '52f1b3564ceb41b36a12ae6fca2d067e1bd2a11ec64ab3556d31ef6cdd37e12b'


def command(*args):
    return subprocess.run([str(a) for a in args], capture_output=True, text=True, check=True)


def plan(core, store, selected):
    command(sys.executable, ROOT.parent/'planner/plan.py', '--compiler', COMPILER,
            '--core', core, '--knowledge-root', store.root, '--snapshot', store.data/'snapshot.json',
            '--budget', 4096, '-o', selected)
    return json.loads(command(COMPILER, 'check-selection', core, selected).stdout)


class Compute2LawTests(unittest.TestCase):
    def test_eighteen_deterministic_new_statements_and_ids(self):
        entries = [semantic_entry(law) for _, law in named_laws()]
        ids = [identity(obj) for obj in entries]
        self.assertEqual(len(ids), 18)
        self.assertEqual(len(set(ids)), 18)
        self.assertEqual(ids, [identity(semantic_entry(law)) for _, law in named_laws()])
        old = Store(ROOT, ROOT/f'store/snapshots/{BASELINE}.json')
        self.assertEqual(len(old.members()), 732)
        self.assertFalse(set(ids) & set(old.members()))
        statements = {(canonical(obj['payload']['from']), canonical(obj['payload']['to'])) for obj in entries}
        for identifier in old.members():
            obj = old.object(identifier)
            if obj['kind'] == 'rewrite':
                self.assertNotIn((canonical(obj['payload']['from']), canonical(obj['payload']['to'])), statements)
        self.assertNotIn('F32', json.dumps(entries))

    def test_independent_literal_recurrence_at_zero_and_word_boundaries(self):
        spec = importlib.util.spec_from_file_location('compute2_oracle', ROOT/'research/web-stack-proofs-2/compute/oracle.py')
        oracle = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(oracle)
        randoms = random.Random(72832)
        for bits in (32,64):
            mask = (1<<bits)-1
            cases = [0,1,mask,mask-2,1<<(bits-1)] + [randoms.getrandbits(bits) for _ in range(8)]
            for degree in (4,5):
                for x,k in zip(cases, reversed(cases)):
                    self.assertEqual(oracle.literal_difference(x,k,degree,bits), pow(k,degree,1<<bits))
                    for n in (0,1,2,17,1024):
                        for invariant in (False,True):
                            self.assertEqual(oracle.original_repeat(x,k,degree,n,bits,invariant),
                                             oracle.closed_repeat(x,k,degree,n,bits,invariant))

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler absent; set INK_COMPILER')
    def test_all_admitted_and_all_types_selected_replayed_reified(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            store, manifest = publish(root/'new')
            for t in ('u32','i32','u64'):
                with self.subTest(type=t):
                    source, core, selected = root/f'{t}.ink',root/f'{t}.core.json',root/f'{t}.selection.json'
                    source.write_text(representative_source(all_families=True).replace('u32',t))
                    command(COMPILER,'emit-core',source,'-o',core)
                    admitted = json.loads(command(COMPILER,'knowledge-check',core,store.root/'view.json').stdout)
                    self.assertEqual(set(admitted['entries']), set(manifest['names'].values()))
                    receipt = plan(core, store, selected)
                    expected = {i for name,i in manifest['names'].items() if name.endswith('_'+t)}
                    self.assertEqual(set(receipt['applied_laws']), expected)
                    command(COMPILER,'emit-core',source,'--selection',selected,'-o',root/f'{t}.selected.json')
                    result = json.loads((root/f'{t}.selected.json').read_text())
                    self.assertNotIn('repeat', json.dumps([f['body'] for f in result['program']['functions']]))

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler absent; set INK_COMPILER')
    def test_old732_unchanged_union750_improves_each_representative(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            old = Store(ROOT, ROOT/f'store/snapshots/{BASELINE}.json')
            old_objects = [old.object(i) for i in sorted(old.members())]
            isolated = Store.publish(root/'old',old_objects)
            isolated.rebuild()
            fresh, manifest = publish(root/'fresh')
            union = Store.publish(root/'union',old_objects+[fresh.object(i) for i in sorted(fresh.members())])
            union.rebuild()
            source,core = root/'input.ink',root/'input.core.json'
            source.write_text(representative_source())
            emitted = json.loads(command(COMPILER,'emit-core',source,'-o',core).stdout)
            prior = plan(core,isolated,root/'old.selection.json')
            self.assertEqual(prior['applied_laws'],[])
            self.assertEqual(prior['selected_core_sha256'],emitted['core_sha256'])
            receipt = plan(core,union,root/'new.selection.json')
            self.assertNotEqual(receipt['selected_core_sha256'],prior['selected_core_sha256'])
            package = json.loads((root/'new.selection.json').read_text())
            for name in ('quartic_repeat','quintic_repeat','quartic_map'):
                self.assertTrue({a['law'] for a in package['applications'] if a['function']==name} & set(manifest['names'].values()))

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler absent; set INK_COMPILER')
    def test_hash_valid_false_repeat_and_map_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source,core = root/'source.ink',root/'core.json'
            source.write_text(representative_source())
            command(COMPILER,'emit-core',source,'-o',core)
            laws = dict(named_laws())
            for name in ('repeat_quartic_increment_u32','map_quintic_difference_u64'):
                with self.subTest(law=name):
                    forged = copy.deepcopy(laws[name])
                    # Wrongly erase all work while retaining a valid content hash.
                    forged['to'] = forged['from']['node']['Op'][1][1 if name.startswith('repeat') else 0]
                    obj = semantic_entry(forged)
                    store = Store.publish(root/name,[obj])
                    view = store.root/'view.json'
                    view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
                    result = subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True)
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn('semantic normal forms differ',result.stderr)
                    self.assertNotIn('identity mismatch',result.stderr)


if __name__ == '__main__':
    unittest.main()
