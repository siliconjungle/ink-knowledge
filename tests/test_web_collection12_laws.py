"""Admission, default old/new discovery, source reification and false controls."""
import copy
import hashlib
import json
import math
import os
import random
from pathlib import Path
import subprocess
import struct
import sys
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.web_collection12_laws import named_laws, publish, source_functions

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
BASELINE = ROOT/'store/snapshots/42bb207446a7ea92fc099ef27d611201f39a1d660c36b147bd11f68fa61a3e90.json'


class Collection12Tests(unittest.TestCase):
    def setUp(self):
        self.receipts = []
        archive = os.environ.get('INK_COLLECTION12_EVIDENCE')
        if archive:
            self.directory = Path(archive).resolve()/self._testMethodName
            self.directory.mkdir(parents=True, exist_ok=True)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='ink-collection12-')
            self.directory = Path(self.temporary.name)

    def tearDown(self):
        if os.environ.get('INK_COLLECTION12_EVIDENCE'):
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
            triples = [([], 0.25, -2.0), ([0.0, -0.0, 1.5, -2.0], 0.25, -2.0),
                       ([65536.0, -0.5, 1.0], -1.0, 0.5),
                       ([{'F32Bits': 0x7fc00000}, {'F32Bits': 0x7f800000},
                         {'F32Bits': 0xff800000}, -0.0], 0.25, -2.0),
                       ([0.0, -0.0, 1.5, -2.0], {'F32Bits': 0x7fc00000}, 2.0),
                       ([0.0, -0.0, 1.5, -2.0], -0.0, {'F32Bits': 0x7fc00000}),
                       ([0.0, -0.0, 1.0, -1.0], 0.0, -0.0)]
        elif t == 'i32':
            triples = [([], -1, -1), ([-(1<<31), -1, (1<<31)-1, 0], 7, 2),
                       ([(1<<31)-1, 1], -(1<<31), -1)]
        else:
            bits = 64 if t == 'u64' else 32
            maximum = (1<<bits)-1
            triples = [([], maximum, maximum), ([maximum, 0, 1<<(bits-1), 1], 7, 2),
                       ([maximum-1, 17], maximum, maximum)]
        rng = random.Random(8)
        for length in (17, 31):
            if t == 'f32':
                triples.append(([rng.randint(-8192, 8192)/8 for _ in range(length)],
                                rng.randint(-4096, 4096)/16, rng.randint(-256, 256)/16))
            else:
                bits = 64 if t == 'u64' else 32
                def number():
                    value = rng.getrandbits(bits)
                    return value-(1<<32) if t == 'i32' and value >= 1<<31 else value
                triples.append(([number() for _ in range(length)], number(), number()))
        for xs, seed, k in triples:
            arguments = [xs, seed, k]
            if t == 'f32':
                def decode(number):
                    return struct.unpack('<f', struct.pack('<I', number['F32Bits']))[0] if isinstance(number, dict) else number
                seed, k = decode(seed), decode(k)
            def normalize(number):
                if t == 'f32':
                    try:
                        return struct.unpack('<f', struct.pack('<f', number))[0]
                    except OverflowError:
                        return math.copysign(math.inf, number)
                bits = 64 if t == 'u64' else 32
                number &= (1<<bits)-1
                return number-(1<<32) if t == 'i32' and number >= 1<<31 else number
            expected = []
            for x in xs:
                if isinstance(x, dict):
                    x = struct.unpack('<f', struct.pack('<I', x['F32Bits']))[0]
                if name.startswith('gated_left_'):
                    chosen = normalize(normalize(x*x)+seed) if x<seed else x
                    output = normalize(normalize(chosen*k)+seed)
                elif name.startswith('gated_right_'):
                    chosen = x if x<seed else normalize(normalize(x*x)+seed)
                    output = normalize(normalize(chosen*k)+seed)
                else:
                    chosen = normalize(normalize(x*x)+seed) if seed<k else normalize(normalize(x*k)-seed)
                    output = normalize(chosen+seed)
                if t == 'f32' and not math.isfinite(output):
                    output = {'F32Bits': struct.unpack('<I', struct.pack('<f', output))[0]}
                expected.append(output)
            yield arguments, expected

    def result_key(self, name, result):
        if name.endswith('_f32'):
            return [x['F32Bits'] if isinstance(x, dict) else struct.unpack('<I', struct.pack('<f', x))[0]
                    for x in result]
        return result

    def test_deterministic_fresh_statements_against_pinned_956(self):
        laws = named_laws()
        objects = [semantic_entry(candidate) for _, candidate in laws]
        ids = [identity(obj) for obj in objects]
        self.assertEqual(len(ids), 12)
        self.assertEqual(len(set(ids)), 12)
        self.assertEqual(ids, [identity(semantic_entry(candidate)) for _, candidate in named_laws()])
        old = Store(ROOT, BASELINE)
        self.assertEqual(len(old.members()), 956)
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
        source.write_text('module Collection12;\n'+'\n'.join(text for _, text in functions)+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        admitted = json.loads(self.run_command(COMPILER, 'knowledge-check', core, isolated.root/'view.json').stdout)
        self.assertEqual(set(admitted['entries']), set(manifest['names'].values()))
        (root/'admission.json').write_text(json.dumps(admitted, indent=2)+'\n')
        applied = set()
        interpreter_results = []
        for index in range(0, len(functions), 5):
            group = functions[index:index+5]
            source, core = root/f'group-{index}.ink', root/f'group-{index}.core.json'
            source.write_text('module Collection12;\n'+'\n'.join(text for _, text in group)+'\n')
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
        self.assertEqual(len(interpreter_results), 72)
        (root/'interpreter-results.json').write_text(json.dumps(interpreter_results, indent=2)+'\n')
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), before)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_hash_valid_wrong_gate_and_mode_comparison_rejected(self):
        root = self.directory
        source, core = root/'input.ink', root/'input.core.json'
        source.write_text('module Collection12;\n'+'\n'.join(text for _, text in source_functions())+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        named = dict(named_laws())
        wrong_gate = copy.deepcopy(named['gated_left_mapped_zip_f32'])
        chosen = wrong_gate['to']['node']['Op'][1][1]['node']['Lambda']['node']['Op'][1][1]
        arguments = chosen['node']['Op'][1]
        arguments[1], arguments[2] = arguments[2], arguments[1]
        wrong_mode = copy.deepcopy(named['mode_selected_mapped_zip_u32'])
        chosen = wrong_mode['to']['node']['Op'][1][1]['node']['Lambda']['node']['Op'][1][1]
        chosen['node']['Op'][1][0]['node']['Op'][0] = 'binary:=='
        for name, forged in [('wrong-gate-branches', wrong_gate), ('equality-instead-of-mode-order', wrong_mode)]:
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
