"""Admission, default old/new discovery, source reification and false controls."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import struct
import sys
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.web_lookup5_laws import named_laws, publish, source_functions

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
BASELINE = ROOT/'store/snapshots/388e3ebd2714c88bc66ae9219102284162f4f65cbed359283f54896b3cfac87c.json'


class Lookup5Tests(unittest.TestCase):
    def setUp(self):
        self.receipts = []
        archive = os.environ.get('INK_LOOKUP5_EVIDENCE')
        if archive:
            self.directory = Path(archive).resolve()/self._testMethodName
            self.directory.mkdir(parents=True, exist_ok=True)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='ink-lookup5-')
            self.directory = Path(self.temporary.name)

    def tearDown(self):
        if os.environ.get('INK_LOOKUP5_EVIDENCE'):
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

    def interpreter_frames(self, name):
        t = name.rsplit('_', 1)[1]
        if t == 'f32':
            triples = [([], -0.0, 2.0, -0.0),
                       ([1.5, {'F32Bits': 0x7fc01234}], -2.0, -2.0, 0.25),
                       ([-0.0, {'F32Bits': 0x7f800000}], 2.0, -1.0, 1.0)]
        elif t == 'i32':
            triples = [([], -(1<<31), -1, -1),
                       ([(1<<31)-1, -(1<<31), 0], 123, 2, 7),
                       ([-(1<<31), (1<<31)-1], 123, -1, -(1<<31))]
        else:
            bits = 64 if t == 'u64' else 32
            maximum = (1<<bits)-1
            triples = [([], maximum, maximum, maximum),
                       ([maximum, 0, 1<<(bits-1)], 123, 2, 7),
                       ([0, maximum], 123, maximum, maximum)]
        for xs, z, k, c in triples:
            item = xs[0] if xs else z
            if name.startswith('threshold_head_'):
                expected = item < k
            elif t == 'f32':
                expected = struct.unpack('<f', struct.pack('<f', item*k))[0]
                if name.startswith('affine_head_'):
                    expected = struct.unpack('<f', struct.pack('<f', expected+c))[0]
            else:
                bits = 64 if t == 'u64' else 32
                expected = (item*k + (c if name.startswith('affine_head_') else 0)) & ((1<<bits)-1)
                if t == 'i32' and expected >= 1<<31:
                    expected -= 1<<32
            args = [xs, z, k]
            if name.startswith('affine_head_'):
                args.append(c)
            yield args, expected

    def result_key(self, name, result):
        if name.endswith('_f32') and not name.startswith('threshold_head_'):
            if isinstance(result, dict):
                return result['F32Bits']
            return struct.unpack('<I', struct.pack('<f', result))[0]
        return result

    def test_deterministic_fresh_statements_against_pinned_809(self):
        laws = named_laws()
        objects = [semantic_entry(candidate) for _, candidate in laws]
        ids = [identity(obj) for obj in objects]
        self.assertEqual(len(ids), 12)
        self.assertEqual(len(set(ids)), 12)
        self.assertEqual(ids, [identity(semantic_entry(candidate)) for _, candidate in named_laws()])
        old = Store(ROOT, BASELINE)
        self.assertEqual(len(old.members()), 809)
        self.assertFalse(set(ids)&set(old.members()))
        endpoints = {(canonical(obj['payload']['from']), canonical(obj['payload']['to'])) for obj in objects}
        for identifier in old.members():
            previous = old.object(identifier)
            if previous['kind'] == 'rewrite' and 'from' in previous['payload']:
                self.assertNotIn((canonical(previous['payload']['from']), canonical(previous['payload']['to'])), endpoints)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen concat compiler required')
    def test_all_twelve_admit_default_select_and_reify_while_prior_retains_work(self):
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
        source.write_text('module Lookup5;\n'+'\n'.join(text for _, text in functions)+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        admitted = json.loads(self.run_command(COMPILER, 'knowledge-check', core, isolated.root/'view.json').stdout)
        self.assertEqual(set(admitted['entries']), set(manifest['names'].values()))
        (root/'admission.json').write_text(json.dumps(admitted, indent=2)+'\n')
        applied = set()
        interpreter_results = []
        for index in range(0, len(functions), 5):
            group = functions[index:index+5]
            source, core = root/f'group-{index}.ink', root/f'group-{index}.core.json'
            source.write_text('module Lookup5;\n'+'\n'.join(text for _, text in group)+'\n')
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
                        for frame_index, (args, expected) in enumerate(self.interpreter_frames(name)):
                            args_file = root/f'{name}-frame-{frame_index}.json'
                            args_file.write_text(json.dumps(args)+'\n')
                            literal = json.loads(self.run_command(COMPILER, 'run', source, name, args_file).stdout)
                            selected = json.loads(self.run_command(COMPILER, 'run', source, name, args_file,
                                                                 '--selection', selection).stdout)
                            self.assertEqual(self.result_key(name, literal), self.result_key(name, expected))
                            self.assertEqual(self.result_key(name, selected), self.result_key(name, literal))
                            interpreter_results.append(dict(function=name, arguments=args, expected=expected,
                                                            original=literal, selected=selected))
                    applied.update(a['law'] for a in package['applications'])
        self.assertTrue(set(manifest['names'].values()) <= applied)
        self.assertEqual(len(interpreter_results), 36)
        (root/'interpreter-results.json').write_text(json.dumps(interpreter_results, indent=2)+'\n')
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), before)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_hash_valid_wrong_index_and_unmapped_fallback_rejected(self):
        root = self.directory
        source, core = root/'input.ink', root/'input.core.json'
        source.write_text('module Lookup5;\n'+'\n'.join(text for _, text in source_functions())+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        named = dict(named_laws())
        wrong_index = copy.deepcopy(named['scaled_head_u32'])
        head = wrong_index['to']['node']['Op'][1][0]
        head['node']['Op'][1][1]['node']['Word'] = 1
        wrong_fallback = copy.deepcopy(named['scaled_head_f32'])
        original_fallback = wrong_fallback['from']['node']['Op'][1][2]
        wrong_fallback['from']['node']['Op'][1][2] = original_fallback['node']['Op'][1][0]
        for name, forged in [('wrong-index', wrong_index), ('unmapped-fallback', wrong_fallback)]:
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
