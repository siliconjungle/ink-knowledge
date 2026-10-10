"""Generic consumer skipping: independent oracles, default replay and false proofs."""
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import random
import struct
import subprocess
import sys
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.semantic_laws import op, value, word
from producers.web_reduction14_laws import heldout_functions, named_laws, publish, source_functions

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
BASELINE = ROOT/'store/snapshots/30e427bcb8524fe3760881a3a5722c7445f9fdab3d2818a707b8d8508e80c110.json'
COMPILER_SHA = '45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08'


def decode(x):
    return struct.unpack('<f', struct.pack('<I', x['F32Bits']))[0] if isinstance(x, dict) else x


def normalize(t, x):
    if t == 'f32':
        try:
            return struct.unpack('<f', struct.pack('<f', x))[0]
        except OverflowError:
            return math.copysign(math.inf, x)
    bits = 64 if t == 'u64' else 32
    x &= (1 << bits)-1
    return x-(1 << bits) if t == 'i32' and x >= 1 << (bits-1) else x


def result_key(t, x):
    if t != 'f32':
        return x
    bits = x['F32Bits'] if isinstance(x, dict) else struct.unpack('<I', struct.pack('<f', x))[0]
    return bits


def frames(t):
    if t == 'f32':
        triples = [([], 0.25, -2.0), ([0.0, -0.0, 1.5, -2.0], 0.25, -2.0),
                   ([65536.0, -0.5, 1.0], -1.0, 0.5),
                   ([{'F32Bits': 0x7fc00000}, {'F32Bits': 0x7f800000}, -0.0], 0.25, -2.0),
                   ([0.0, -0.0, 1.5], {'F32Bits': 0x7fc00000}, 2.0),
                   ([-0.0, 0.0], 0.0, -0.0)]
    else:
        bits = 64 if t == 'u64' else 32
        lo, hi = (-(1<<31), (1<<31)-1) if t == 'i32' else (0, (1<<bits)-1)
        triples = [([], hi, hi), ([lo, hi, 0, 1], 7, 2), ([hi, 1], lo, -1 if t == 'i32' else hi)]
        rng = random.Random(14)
        for n in (1, 17, 31):
            number = lambda: rng.randint(lo, hi)
            triples.append(([number() for _ in range(n)], number(), number()))
    for index, (xs, seed, k) in enumerate(triples):
        # Independent second list: include empty and a nonempty suffix when xs is empty.
        ys = [seed, k] if index % 2 == 0 else []
        yield xs, ys, seed, k


def original_and_oracle(name, xs, ys, seed, k, heldout=False):
    t = name.rsplit('_', 1)[1]
    xs, ys, seed, k = [decode(x) for x in xs], [decode(x) for x in ys], decode(seed), decode(k)
    wrap = lambda n: normalize(t, n)
    f = (lambda x: k if x > k else x) if heldout else (lambda x: seed if x < seed else x)
    if name.startswith('callback_mapped_head'):
        mapped = [f(x) for x in xs]
        fallback = k if heldout else seed
        output = (lambda x: wrap(x-seed)) if heldout else (lambda x: wrap(x*k))
        original = output(mapped[0] if mapped else fallback)
        oracle = output(f(xs[0] if xs else fallback))
    elif name.startswith('concat_first_result'):
        concatenated = xs+ys
        fallback = k if heldout else seed
        output = (lambda x: wrap(x-seed)) if heldout else (lambda x: wrap(x+k))
        original = output(concatenated[0] if concatenated else fallback)
        oracle = output(xs[0] if xs else ys[0] if ys else fallback)
    else:
        zipped = ([wrap(wrap(a*k)-seed) if a == b else wrap(b+seed) for a, b in zip(xs, xs)] if heldout else [wrap(wrap(a*k)+b) if a < seed else wrap(b-seed) for a, b in zip(xs, xs)])
        original, oracle = len(zipped), len(xs)
    return original, oracle


class Reduction14Tests(unittest.TestCase):
    def setUp(self):
        self.receipts = []
        archive = os.environ.get('INK_REDUCTION14_EVIDENCE')
        if archive:
            self.directory = Path(archive).resolve()/self._testMethodName
            self.directory.mkdir(parents=True, exist_ok=True)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='ink-reduction14-')
            self.directory = Path(self.temporary.name)

    def tearDown(self):
        if os.environ.get('INK_REDUCTION14_EVIDENCE'):
            (self.directory/'commands.json').write_text(json.dumps(self.receipts, indent=2)+'\n')
        elif hasattr(self, 'temporary'):
            self.temporary.cleanup()

    def run_command(self, *args, success=True):
        argv = list(map(str, args))
        r = subprocess.run(argv, capture_output=True, text=True)
        self.receipts.append(dict(argv=argv, exit_code=r.returncode, stdout=r.stdout, stderr=r.stderr))
        if success:
            self.assertEqual(r.returncode, 0, r.stderr)
        return r

    def source(self, functions, prefix='all'):
        source, core = self.directory/f'{prefix}.ink', self.directory/f'{prefix}.core.json'
        source.write_text('module Reduction14;\n'+'\n'.join(text for _, text in functions)+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        return source, core

    def test_deterministic_fresh_statements_against_pinned_998(self):
        objects = [semantic_entry(law) for _, law in named_laws()]
        ids = [identity(o) for o in objects]
        self.assertEqual(len(ids), 12)
        self.assertEqual(len(set(ids)), 12)
        self.assertEqual(ids, [identity(semantic_entry(law)) for _, law in named_laws()])
        old = Store(ROOT, BASELINE)
        self.assertEqual(len(old.members()), 998)
        self.assertFalse(set(ids)&set(old.members()))
        endpoints = {(canonical(o['payload']['from']), canonical(o['payload']['to'])) for o in objects}
        for i in old.members():
            o = old.object(i)
            if o['kind'] == 'rewrite' and 'from' in o['payload']:
                self.assertNotIn((canonical(o['payload']['from']), canonical(o['payload']['to'])), endpoints)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_admission_and_all_typed_original_interpreter_oracles(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), COMPILER_SHA)
        isolated, manifest = publish(self.directory/'isolated')
        source, core = self.source(source_functions())
        receipt = json.loads(self.run_command(COMPILER, 'knowledge-check', core, isolated.root/'view.json').stdout)
        self.assertEqual(set(receipt['entries']), set(manifest['names'].values()))
        rows = []
        for name, _ in source_functions():
            t = name.rsplit('_', 1)[1]
            for index, (xs, ys, seed, k) in enumerate(frames(t)):
                args = [xs, ys, seed, k] if name.startswith('concat_first_result') else [xs, seed, k]
                original, oracle = original_and_oracle(name, xs, ys, seed, k)
                result_type = 'u64' if name.startswith('self_zip_cardinality') else t
                self.assertEqual(result_key(result_type, original), result_key(result_type, oracle))
                path = self.directory/f'{name}-{index}.args.json'
                path.write_text(json.dumps(args)+'\n')
                actual = json.loads(self.run_command(COMPILER, 'run', source, name, path).stdout)
                self.assertEqual(result_key(result_type, actual), result_key(result_type, oracle))
                rows.append(dict(function=name, arguments=args, interpreter=actual, oracle_key=result_key(result_type, oracle)))
        self.assertEqual(len(rows), 72)
        (self.directory/'interpreter-results.json').write_text(json.dumps(rows, indent=2)+'\n')

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_hash_valid_false_fallback_order_and_cardinality_rejected(self):
        _, core = self.source(source_functions())
        named = dict(named_laws())
        wrong_head = copy.deepcopy(named['callback_mapped_head_u32'])
        # An empty mapped list must return f(z), not an unrelated constant.
        wrong_head['to'] = word('U32', 1)
        wrong_concat = copy.deepcopy(named['concat_first_result_u32'])
        outer = wrong_concat['to']['node']['Op'][1]
        inner = outer[2]['node']['Op'][1]
        outer[0], inner[0] = inner[0], outer[0]
        wrong_count = copy.deepcopy(named['self_zip_cardinality_u32'])
        wrong_count['to'] = op(value('U64'), 'binary:+', wrong_count['to'], word('U64', 1))
        for name, candidate in [('wrong-fallback', wrong_head), ('reversed-prefix', wrong_concat), ('off-by-one-count', wrong_count)]:
            obj = semantic_entry(candidate)
            store = Store.publish(self.directory/name, [obj])
            view = store.root/'view.json'
            view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
            r = self.run_command(COMPILER, 'knowledge-check', core, view, success=False)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn('semantic normal forms differ', r.stderr)
            self.assertNotIn('identity mismatch', r.stderr)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_default_old_and_new_selection_replay_reify_selected_interpreter(self):
        isolated, manifest = publish(self.directory/'isolated')
        pinned = Store(ROOT, BASELINE)
        old = Store.publish(self.directory/'prior', [pinned.object(i) for i in sorted(pinned.members())]); old.rebuild()
        combined = Store.publish(self.directory/'combined', [old.object(i) for i in sorted(old.members())]+[isolated.object(i) for i in sorted(isolated.members())]); combined.rebuild()
        rows = []
        functions = source_functions()
        for index in range(0, len(functions), 3):
            group = functions[index:index+3]
            source, core = self.source(group, f'group-{index}')
            original = json.loads(core.read_text())['program']['functions']
            original_bodies = {f['name']: f['body'] for f in original}
            for label, store in [('prior', old), ('new', combined)]:
                selection = self.directory/f'group-{index}-{label}.selection.json'
                self.run_command(sys.executable, ROOT.parent/'planner/plan.py', '--compiler', COMPILER, '--core', core,
                    '--knowledge-root', store.root, '--snapshot', store.data/'snapshot.json', '--budget', 4096, '-o', selection)
                package = json.loads(selection.read_text())
                self.run_command(COMPILER, 'check-selection', core, selection)
                selected = self.directory/f'group-{index}-{label}.selected.core.json'
                self.run_command(COMPILER, 'emit-core', source, '--selection', selection, '-o', selected)
                bodies = {f['name']: f['body'] for f in json.loads(selected.read_text())['program']['functions']}
                if label == 'prior':
                    self.assertEqual(package['applications'], [])
                    self.assertEqual(bodies, original_bodies)
                else:
                    for name, _ in group:
                        self.assertEqual([a['law'] for a in package['applications'] if a['function'] == name], [manifest['names'][name]])
                        self.assertNotEqual(bodies[name], original_bodies[name])
                        chosen = [a for a in package['applications'] if a['function'] == name][0]
                        self.assertEqual(chosen['premises'], ['Normalize'] if name.startswith('callback_mapped_head') else [])
                        t = name.rsplit('_', 1)[1]
                        result_type = 'u64' if name.startswith('self_zip_cardinality') else t
                        for frame_index, (xs, ys, seed, k) in enumerate(frames(t)):
                            args = [xs, ys, seed, k] if name.startswith('concat_first_result') else [xs, seed, k]
                            _, oracle = original_and_oracle(name, xs, ys, seed, k)
                            path = self.directory/f'{name}-{frame_index}.args.json';path.write_text(json.dumps(args)+'\n')
                            actual = json.loads(self.run_command(COMPILER, 'run', source, name, path, '--selection', selection).stdout)
                            self.assertEqual(result_key(result_type, actual), result_key(result_type, oracle))
                            rows.append(dict(function=name, arguments=args, selected=actual, oracle_key=result_key(result_type, oracle)))
        self.assertEqual(len(rows), 72)
        (self.directory/'selected-interpreter-results.json').write_text(json.dumps(rows, indent=2)+'\n')
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), COMPILER_SHA)


    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_heldout_callbacks_same_generic_laws_natural_selection_and_oracles(self):
        isolated, manifest = publish(self.directory/'isolated')
        pinned = Store(ROOT, BASELINE)
        old = Store.publish(self.directory/'prior', [pinned.object(i) for i in sorted(pinned.members())]); old.rebuild()
        combined = Store.publish(self.directory/'combined', [old.object(i) for i in sorted(old.members())]+[isolated.object(i) for i in sorted(isolated.members())]); combined.rebuild()
        functions = heldout_functions()[:3]
        source, core = self.source(functions, 'heldout')
        original = json.loads(core.read_text())['program']['functions']
        original_bodies = {f['name']: f['body'] for f in original}
        rows = []
        for label, store in [('prior', old), ('new', combined)]:
            selection = self.directory/f'{label}.selection.json'
            self.run_command(sys.executable, ROOT.parent/'planner/plan.py', '--compiler', COMPILER, '--core', core,
                '--knowledge-root', store.root, '--snapshot', store.data/'snapshot.json', '--budget', 4096, '-o', selection)
            package = json.loads(selection.read_text())
            self.run_command(COMPILER, 'check-selection', core, selection)
            selected = self.directory/f'{label}.selected.core.json'
            self.run_command(COMPILER, 'emit-core', source, '--selection', selection, '-o', selected)
            bodies = {f['name']: f['body'] for f in json.loads(selected.read_text())['program']['functions']}
            if label == 'prior':
                self.assertEqual(package['applications'], [])
                self.assertEqual(bodies, original_bodies)
            else:
                for law_name, text in functions:
                    name = text.split('fn ', 1)[1].split('(', 1)[0]
                    self.assertEqual([a['law'] for a in package['applications'] if a['function'] == name], [manifest['names'][law_name]])
                    self.assertNotEqual(bodies[name], original_bodies[name])
                    chosen = [a for a in package['applications'] if a['function'] == name][0]
                    self.assertEqual(chosen['premises'], ['Normalize'] if law_name.startswith('callback_mapped_head') else [])
                    for index, (xs, ys, seed, k) in enumerate(frames('u32')):
                        args = [xs, ys, seed, k] if law_name.startswith('concat_first_result') else [xs, seed, k]
                        literal, oracle = original_and_oracle(law_name, xs, ys, seed, k, heldout=True)
                        self.assertEqual(literal, oracle)
                        path = self.directory/f'{name}-{index}.args.json';path.write_text(json.dumps(args)+'\n')
                        actual_original = json.loads(self.run_command(COMPILER, 'run', source, name, path).stdout)
                        actual_selected = json.loads(self.run_command(COMPILER, 'run', source, name, path, '--selection', selection).stdout)
                        self.assertEqual(actual_original, oracle)
                        self.assertEqual(actual_selected, oracle)
                        rows.append(dict(function=name, arguments=args, original=actual_original, selected=actual_selected, oracle=oracle))
        self.assertEqual(len(rows), 18)
        (self.directory/'interpreter-results.json').write_text(json.dumps(rows, indent=2)+'\n')

if __name__ == '__main__':
    unittest.main()
