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
from producers.web_compute3_laws import named_laws, publish, representative_source

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent / 'toolchain/ink-sequence-proofs'))
BASELINE = '7ecbce6e14b1273e771e4634b61e92d0f85929934c0d4e165b1f14c7c8660c6c'


def command(*args):
    return subprocess.run([str(a) for a in args], capture_output=True, text=True, check=True)


def plan(core, store, selected):
    command(sys.executable, ROOT.parent/'planner/plan.py', '--compiler', COMPILER,
            '--core', core, '--knowledge-root', store.root, '--snapshot', store.data/'snapshot.json',
            '--budget', 4096, '-o', selected)
    return json.loads(command(COMPILER, 'check-selection', core, selected).stdout)


class Compute3LawTests(unittest.TestCase):
    def test_nine_deterministic_new_statements_and_ids(self):
        entries = [semantic_entry(law) for _, law in named_laws()]
        ids = [identity(obj) for obj in entries]
        self.assertEqual(len(ids), 9)
        self.assertEqual(len(set(ids)), 9)
        self.assertEqual(ids, [identity(semantic_entry(law)) for _, law in named_laws()])
        old = Store(ROOT, ROOT/f'store/snapshots/{BASELINE}.json')
        self.assertEqual(len(old.members()), 765)
        self.assertFalse(set(ids) & set(old.members()))
        statements = {(canonical(obj['payload']['from']), canonical(obj['payload']['to'])) for obj in entries}
        for identifier in old.members():
            obj = old.object(identifier)
            if obj['kind'] == 'rewrite':
                self.assertNotIn((canonical(obj['payload']['from']), canonical(obj['payload']['to'])), statements)
        self.assertNotIn('F32', json.dumps(entries))

    def test_independent_literal_recurrence_at_zero_and_word_boundaries(self):
        spec = importlib.util.spec_from_file_location('compute3_oracle', ROOT/'research/web-stack-proofs-3/compute/oracle.py')
        oracle = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(oracle)
        randoms = random.Random(76503)
        for t in ('u32','i32','u64'):
            bits = 64 if t == 'u64' else 32
            mask = (1<<bits)-1
            xs = [oracle.native(v,t) for v in [0,1,mask,mask-2,1<<(bits-1)] + [randoms.getrandbits(bits) for _ in range(8)]]
            for seed in (oracle.native(1,t),oracle.native(mask-2,t)):
                k = oracle.native(mask-2,t)
                self.assertTrue(any(x < seed for x in xs))
                self.assertTrue(any(x >= seed for x in xs))
                for function in ('captured_branch_repeat','affine_blend_repeat','captured_mask_repeat'):
                    for n in (0,1,2,17,256):
                        self.assertEqual(oracle.original(function,xs,seed,k,n,t),oracle.closed(function,xs,seed,k,n,t))

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler absent; set INK_COMPILER')
    def test_all_admitted_and_all_types_selected_replayed_reified(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            store, manifest = publish(root/'new')
            for t in ('u32','i32','u64'):
                with self.subTest(type=t):
                    source, core, selected = root/f'{t}.ink',root/f'{t}.core.json',root/f'{t}.selection.json'
                    source.write_text(representative_source(t=t))
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
    def test_old765_unchanged_union774_improves_each_representative(self):
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
            for name in ('captured_branch_repeat','affine_blend_repeat','captured_mask_repeat'):
                self.assertTrue({a['law'] for a in package['applications'] if a['function']==name} & set(manifest['names'].values()))

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler absent; set INK_COMPILER')
    def test_hash_valid_false_recurrences_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source,core = root/'source.ink',root/'core.json'
            source.write_text(representative_source())
            command(COMPILER,'emit-core',source,'-o',core)
            laws = dict(named_laws())
            for name in ('captured_branch_repeat_u32','affine_blend_repeat_u64','captured_projection_repeat_i32'):
                with self.subTest(law=name):
                    forged = copy.deepcopy(laws[name])
                    # Wrongly erase all work while retaining a valid content hash.
                    forged['to'] = forged['from']['node']['Op'][1][1]
                    if name.startswith('captured_projection'):
                        from producers.semantic_laws import var, value
                        forged['to'] = var(value('I32'),'x')
                    obj = semantic_entry(forged)
                    store = Store.publish(root/name,[obj])
                    view = store.root/'view.json'
                    view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
                    result = subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True)
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn('semantic normal forms differ',result.stderr)
                    self.assertNotIn('identity mismatch',result.stderr)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler absent; set INK_COMPILER')
    def test_actual_source_and_selected_interpreter_zero_one_and_256_counts(self):
        spec = importlib.util.spec_from_file_location('compute3_source_oracle', ROOT/'research/web-stack-proofs-3/compute/oracle.py')
        oracle = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(oracle)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            store, _ = publish(root/'new')
            for t in ('u32','i32','u64'):
                bits = 64 if t == 'u64' else 32
                mask = (1<<bits)-1
                xs = [oracle.native(x,t) for x in (0,1,2,mask,mask-2,1<<(bits-1))]
                seed, k = 2, oracle.native(mask-2,t)
                self.assertTrue(any(x < seed for x in xs))
                self.assertTrue(any(x >= seed for x in xs))
                args = root/'args.json'
                args.write_text(json.dumps([xs,seed,k]))
                for n in (0,1,256):
                    source,core,selection = root/'input.ink',root/'input.json',root/'selection.json'
                    source.write_text(representative_source(n,t))
                    command(COMPILER,'emit-core',source,'-o',core)
                    plan(core,store,selection)
                    for function in ('captured_branch_repeat','affine_blend_repeat','captured_mask_repeat'):
                        with self.subTest(type=t,count=n,function=function):
                            expected = oracle.closed(function,xs,seed,k,n,t)
                            original = json.loads(command(COMPILER,'run',source,function,args).stdout)
                            selected = json.loads(command(COMPILER,'run',source,function,args,'--selection',selection).stdout)
                            self.assertEqual(original,expected)
                            self.assertEqual(selected,expected)


if __name__ == '__main__':
    unittest.main()
