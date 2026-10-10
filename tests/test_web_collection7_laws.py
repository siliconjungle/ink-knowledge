"""Admission, default old/new discovery, source reification and false controls."""
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
import struct
import sys
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.web_collection7_laws import named_laws, publish, source_functions

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
BASELINE = ROOT/'store/snapshots/97f7f5263af8e184c1b68559220e0182f3beda7802fe0b4ea372faac5d898044.json'


class Collection7Tests(unittest.TestCase):
    def setUp(self):
        self.receipts = []
        archive = os.environ.get('INK_COLLECTION7_EVIDENCE')
        if archive:
            self.directory = Path(archive).resolve()/self._testMethodName
            self.directory.mkdir(parents=True, exist_ok=True)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='ink-collection7-')
            self.directory = Path(self.temporary.name)

    def tearDown(self):
        if os.environ.get('INK_COLLECTION7_EVIDENCE'):
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
                         {'F32Bits': 0xff800000}, -0.0], 0.25, -2.0)]
        elif t == 'i32':
            triples = [([], -1, -1), ([-(1<<31), -1, (1<<31)-1, 0], 7, 2),
                       ([(1<<31)-1, 1], -(1<<31), -1)]
        else:
            bits = 64 if t == 'u64' else 32
            maximum = (1<<bits)-1
            triples = [([], maximum, maximum), ([maximum, 0, 1<<(bits-1), 1], 7, 2),
                       ([maximum-1, 17], maximum, maximum)]
        for xs, seed, k in triples:
            expected = []
            for x in xs:
                if t == 'f32':
                    if isinstance(x, dict):
                        x = struct.unpack('<f', struct.pack('<I', x['F32Bits']))[0]
                    rounded = lambda value: struct.unpack('<f', struct.pack('<f', value))[0]
                    if name.startswith('minimum_'):
                        output = rounded(rounded(x*k)+seed)
                    elif name.startswith('maximum_'):
                        output = rounded(x*k) if x<seed else rounded(x+seed)
                    else:
                        factor = k if x == x else seed
                        output = rounded(rounded(x*factor)+seed)
                    if not math.isfinite(output):
                        output = {'F32Bits': struct.unpack('<I', struct.pack('<f', output))[0]}
                else:
                    bits = 64 if t == 'u64' else 32
                    if name.startswith('minimum_') or name.startswith('equality_'):
                        output = x*k+seed
                    else:
                        output = x*k if x<seed else x+seed
                    output &= (1<<bits)-1
                    if t == 'i32' and output >= 1<<31:
                        output -= 1<<32
                expected.append(output)
            yield [xs, seed, k], expected

    def result_key(self, name, result):
        if name.endswith('_f32'):
            return [x['F32Bits'] if isinstance(x, dict) else struct.unpack('<I', struct.pack('<f', x))[0]
                    for x in result]
        return result

    def test_deterministic_fresh_statements_against_pinned_854(self):
        laws = named_laws()
        objects = [semantic_entry(candidate) for _, candidate in laws]
        ids = [identity(obj) for obj in objects]
        self.assertEqual(len(ids), 12)
        self.assertEqual(len(set(ids)), 12)
        self.assertEqual(ids, [identity(semantic_entry(candidate)) for _, candidate in named_laws()])
        old = Store(ROOT, BASELINE)
        self.assertEqual(len(old.members()), 854)
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
        source.write_text('module Collection7;\n'+'\n'.join(text for _, text in functions)+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        admitted = json.loads(self.run_command(COMPILER, 'knowledge-check', core, isolated.root/'view.json').stdout)
        self.assertEqual(set(admitted['entries']), set(manifest['names'].values()))
        (root/'admission.json').write_text(json.dumps(admitted, indent=2)+'\n')
        applied = set()
        interpreter_results = []
        for index in range(0, len(functions), 5):
            group = functions[index:index+5]
            source, core = root/f'group-{index}.ink', root/f'group-{index}.core.json'
            source.write_text('module Collection7;\n'+'\n'.join(text for _, text in group)+'\n')
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
        self.assertEqual(len(interpreter_results), 39)
        (root/'interpreter-results.json').write_text(json.dumps(interpreter_results, indent=2)+'\n')
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), before)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_hash_valid_negated_value_and_inverted_equality_rejected(self):
        root = self.directory
        source, core = root/'input.ink', root/'input.core.json'
        source.write_text('module Collection7;\n'+'\n'.join(text for _, text in source_functions())+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        named = dict(named_laws())
        wrong_value = copy.deepcopy(named['minimum_zip_postmap_f32'])
        apply = wrong_value['to']['node']['Op'][1][1]['node']['Lambda']
        argument = apply['node']['Op'][1][1]
        apply['node']['Op'][1][1] = dict(sort=argument['sort'], node={'Op':['neg',[argument]]})
        wrong_equality = copy.deepcopy(named['equality_zip_postmap_f32'])
        choose = wrong_equality['to']['node']['Op'][1][1]['node']['Lambda']['node']['Op'][1][1]
        choose['node']['Op'][1][0]['node']['Op'][0] = 'binary:!='
        for name, forged in [('negated-selected-value', wrong_value), ('inverted-self-equality', wrong_equality)]:
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
