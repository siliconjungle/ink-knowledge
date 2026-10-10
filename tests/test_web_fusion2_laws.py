"""Admission, default old/new discovery, source reification and false controls."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.web_fusion2_laws import named_laws, publish, source_functions

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
BASELINE = ROOT/'store/snapshots/52f1b3564ceb41b36a12ae6fca2d067e1bd2a11ec64ab3556d31ef6cdd37e12b.json'


class Fusion2Tests(unittest.TestCase):
    def setUp(self):
        self.receipts = []
        archive = os.environ.get('INK_FUSION2_EVIDENCE')
        if archive:
            self.directory = Path(archive).resolve()/self._testMethodName
            self.directory.mkdir(parents=True, exist_ok=True)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='ink-fusion2-')
            self.directory = Path(self.temporary.name)

    def tearDown(self):
        if os.environ.get('INK_FUSION2_EVIDENCE'):
            (self.directory/'commands.json').write_text(json.dumps(self.receipts, indent=2)+'\n')
        elif hasattr(self, 'temporary'):
            self.temporary.cleanup()

    def run_command(self, *args, success=True):
        argv = list(map(str, args))
        result = subprocess.run(argv, capture_output=True, text=True)
        self.receipts.append(dict(argv=argv, exit_code=result.returncode,
                                  stdout=result.stdout, stderr=result.stderr))
        if success:
            self.assertEqual(result.returncode, 0, result.stderr)
        return result

    def test_deterministic_fresh_statements_against_pinned_732(self):
        laws = named_laws()
        objects = [semantic_entry(candidate) for _, candidate in laws]
        ids = [identity(obj) for obj in objects]
        self.assertEqual(len(ids), 15)
        self.assertEqual(len(set(ids)), 15)
        self.assertEqual(ids, [identity(semantic_entry(candidate)) for _, candidate in named_laws()])
        old = Store(ROOT, BASELINE)
        self.assertEqual(len(old.members()), 732)
        self.assertFalse(set(ids)&set(old.members()))
        endpoints = {(canonical(obj['payload']['from']), canonical(obj['payload']['to'])) for obj in objects}
        for identifier in old.members():
            previous = old.object(identifier)
            if previous['kind'] == 'rewrite' and 'from' in previous['payload']:
                self.assertNotIn((canonical(previous['payload']['from']), canonical(previous['payload']['to'])), endpoints)
        self.assertFalse(any(name.startswith('weighted_self_zip_sum_f32') for name, _ in laws))

    @unittest.skipUnless(COMPILER.is_file(), 'frozen concat compiler required')
    def test_all_fifteen_admit_default_select_and_reify_while_prior_retains_work(self):
        root = self.directory
        before = hashlib.sha256(COMPILER.read_bytes()).hexdigest()
        self.assertEqual(before, '45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        isolated, manifest = publish(root/'isolated')
        previous = Store(ROOT, BASELINE)
        old = Store.publish(root/'prior', [previous.object(i) for i in sorted(previous.members())])
        old.rebuild()
        self.assertEqual(old.snapshot_id, previous.snapshot_id)
        combined = Store.publish(root/'combined', [old.object(i) for i in sorted(old.members())]+[isolated.object(i) for i in sorted(isolated.members())])
        combined.rebuild()
        functions = source_functions()
        source, core = root/'all.ink', root/'all.core.json'
        source.write_text('module Fusion2;\n'+'\n'.join(text for _, text in functions)+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        admitted = json.loads(self.run_command(COMPILER, 'knowledge-check', core, isolated.root/'view.json').stdout)
        self.assertEqual(set(admitted['entries']), set(manifest['names'].values()))
        (root/'admission.json').write_text(json.dumps(admitted, indent=2)+'\n')
        applied = set()
        for index in range(0, len(functions), 5):
            group = functions[index:index+5]
            source, core = root/f'group-{index}.ink', root/f'group-{index}.core.json'
            source.write_text('module Fusion2;\n'+'\n'.join(text for _, text in group)+'\n')
            self.run_command(COMPILER, 'emit-core', source, '-o', core)
            original = json.loads(core.read_text())['program']['functions']
            old_bodies = {f['name']: f['body'] for f in original}
            for label, store in [('prior', old), ('new', combined)]:
                selection = root/f'group-{index}-{label}.selection.json'
                planned = self.run_command(sys.executable, ROOT.parent/'planner/plan.py', '--compiler', COMPILER,
                    '--core', core, '--knowledge-root', store.root, '--snapshot', store.data/'snapshot.json',
                    '--budget', 4096, '-o', selection)
                (root/f'group-{index}-{label}.planner.json').write_text(planned.stdout)
                package = json.loads(selection.read_text())
                checked = self.run_command(COMPILER, 'check-selection', core, selection)
                (root/f'group-{index}-{label}.replay.json').write_text(checked.stdout)
                selected_core = root/f'group-{index}-{label}.selected.core.json'
                self.run_command(COMPILER, 'emit-core', source, '--selection', selection, '-o', selected_core)
                bodies = {f['name']: f['body'] for f in json.loads(selected_core.read_text())['program']['functions']}
                if label == 'prior':
                    self.assertEqual(package['applications'], [])
                    self.assertEqual(bodies, old_bodies)
                else:
                    for name, _ in group:
                        ids = {a['law'] for a in package['applications'] if a['function'] == name}
                        self.assertIn(manifest['names'][name], ids)
                        self.assertNotEqual(bodies[name], old_bodies[name])
                    applied.update(a['law'] for a in package['applications'])
        self.assertTrue(set(manifest['names'].values()) <= applied)
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), before)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen concat compiler required')
    def test_hash_valid_wrong_weight_and_guard_are_semantically_rejected(self):
        root = self.directory
        source, core = root/'input.ink', root/'input.core.json'
        source.write_text('module Fusion2;\n'+'\n'.join(text for _, text in source_functions())+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        named = dict(named_laws())
        wrong_weight = copy.deepcopy(named['weighted_self_zip_sum_u32'])
        wrong_weight['to']['node']['Op'][1][1]['node']['Op'][0] = 'binary:-'
        wrong_guard = copy.deepcopy(named['filter_ordered_fold_f32'])
        arguments = wrong_guard['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']['node']['Op'][1]
        arguments[1], arguments[2] = arguments[2], arguments[1]
        for name, forged in [('wrong-weight', wrong_weight), ('inverted-filter-guard', wrong_guard)]:
            obj = semantic_entry(forged)
            store = Store.publish(root/name, [obj])
            view = store.root/'view.json'
            view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
            rejected = self.run_command(COMPILER, 'knowledge-check', core, view, success=False)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('semantic normal forms differ', rejected.stderr)
            self.assertNotIn('identity mismatch', rejected.stderr)


if __name__ == '__main__':
    unittest.main()
