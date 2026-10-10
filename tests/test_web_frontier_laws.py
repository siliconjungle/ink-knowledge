"""Existing-checker admission, replay, old catalogue control and false proofs."""
import copy
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.semantic_laws import binary, word
from producers.web_frontier_laws import named_laws, publish

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent / 'target/release/ink'))
OLD_SNAPSHOT = '3ba66adca49bc68eee035c2addecf55cea8a9533d25741dc9d48f5d24a213be1'


def source():
    parts = ['module FrontierProofs;']
    for t in ('u32', 'i32', 'u64'):
        parts += [f'fn guard_{t}(x:{t},k:{t})->{t}{{return choose(x==k,k,x);}}',
                  f'fn restore_{t}(x:{t})->{t}{{return repeat(512,x,fn(i)=>fn(acc)=>x);}}']
        if t != 'i32':
            parts.append(f'fn fold_{t}(xs:List<{t}>,k:{t})->{t}{{return foldr(xs,k,fn(x)=>fn(acc)=>choose(x==k,x,acc));}}')
    parts += [
        'fn frontier_guarded_write(xs:List<u32>,seed:u32,factor:u32)->List<u32>{return xs.map(fn(x)=>choose(x==seed,seed,x)+factor);}',
        'fn frontier_repeat_restore(xs:List<u32>,seed:u32,factor:u32)->List<u32>{return xs.map(fn(x)=>repeat(512,x,fn(i)=>fn(acc)=>x)+factor);}',
    ]
    return '\n'.join(parts) + '\n'


def command(*args):
    return subprocess.run([str(a) for a in args], capture_output=True, text=True, check=True)


class FrontierLawTests(unittest.TestCase):
    def test_deterministic_no_existing_statement_duplicates(self):
        objects = [semantic_entry(law) for _, law in named_laws()]
        ids = [identity(obj) for obj in objects]
        self.assertEqual(len(ids), 8)
        self.assertEqual(len(set(ids)), 8)
        self.assertEqual(ids, [identity(semantic_entry(law)) for _, law in named_laws()])
        statements = {(canonical(obj['payload']['from']), canonical(obj['payload']['to'])) for obj in objects}
        for path in (ROOT / 'store/objects').glob('*.json'):
            if path.stem in ids:
                continue  # Repeating this test after publication remains valid.
            old = json.loads(path.read_text())
            if old.get('kind') == 'rewrite':
                payload = old['payload']
                self.assertNotIn((canonical(payload['from']), canonical(payload['to'])), statements)

    @unittest.skipUnless(COMPILER.is_file(), 'build release compiler or set INK_COMPILER')
    def test_admission_all_eight_applications_and_old_catalogue_control(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            store, manifest = publish(root / 'store')
            ink, core, selection = root / 'input.ink', root / 'core.json', root / 'selection.json'
            ink.write_text(source())
            emitted = json.loads(command(COMPILER, 'emit-core', ink, '-o', core).stdout)
            admitted = json.loads(command(COMPILER, 'knowledge-check', core, store.root / 'view.json').stdout)
            self.assertEqual(set(admitted['entries']), set(manifest['names'].values()))
            command(sys.executable, ROOT.parent / 'planner/plan.py', '--compiler', COMPILER,
                    '--core', core, '--knowledge-root', store.root, '--snapshot', store.data / 'snapshot.json',
                    '--budget', 4096, '-o', selection)
            replay = json.loads(command(COMPILER, 'check-selection', core, selection).stdout)
            self.assertEqual(set(replay['applied_laws']), set(manifest['names'].values()))
            package = json.loads(selection.read_text())
            self.assertIn('frontier_guarded_write', {a['function'] for a in package['applications']})
            self.assertIn('frontier_repeat_restore', {a['function'] for a in package['applications']})
            # A disposable index is tied to its active snapshot. Give the old
            # pin its own index instead of using/rebuilding the published one.
            original = Store(ROOT, ROOT / f'store/snapshots/{OLD_SNAPSHOT}.json')
            members = sorted(original.members())
            old_store = Store.publish(root / 'old-knowledge', [original.object(i) for i in members])
            old_store.rebuild()
            self.assertEqual(old_store.snapshot_id, OLD_SNAPSHOT)
            old = root / 'old-selection.json'
            command(sys.executable, ROOT.parent / 'planner/plan.py', '--compiler', COMPILER,
                    '--core', core, '--knowledge-root', old_store.root,
                    '--snapshot', old_store.data / 'snapshot.json',
                    '--budget', 4096, '-o', old)
            old_replay = json.loads(command(COMPILER, 'check-selection', core, old).stdout)
            self.assertEqual(old_replay['applied_laws'], [])
            self.assertEqual(old_replay['selected_core_sha256'], emitted['core_sha256'])
            self.assertNotEqual(replay['selected_core_sha256'], old_replay['selected_core_sha256'])

    @unittest.skipUnless(COMPILER.is_file(), 'build release compiler or set INK_COMPILER')
    def test_hash_valid_false_guard_and_restore_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            ink, core = root / 'input.ink', root / 'core.json'
            ink.write_text(source())
            command(COMPILER, 'emit-core', ink, '-o', core)
            laws = dict(named_laws())
            guard = copy.deepcopy(laws['guarded_same_value_write_u32'])
            branch = guard['from']['node']['Op'][1][2]
            guard['from']['node']['Op'][1][2] = binary('+', branch, word('U32', 1))
            restore = copy.deepcopy(laws['repeat_restore_initial_u32'])
            body = restore['from']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']
            restore['from']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda'] = binary('+', body, word('U32', 1))
            for name, wrong in [('false-guard', guard), ('false-restore', restore)]:
                obj = semantic_entry(wrong)
                store = Store.publish(root / name, [obj])
                view = store.root / 'view.json'
                view.write_bytes(canonical(store.bundle([identity(obj)])) + b'\n')
                rejected = subprocess.run([COMPILER, 'knowledge-check', core, view], capture_output=True, text=True)
                self.assertNotEqual(rejected.returncode, 0)
                self.assertIn('semantic normal forms differ', rejected.stderr)
                self.assertNotIn('identity mismatch', rejected.stderr)


if __name__ == '__main__':
    unittest.main()
