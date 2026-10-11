"""Generic callback admission, prior novelty, executable reuse and false controls."""
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
from producers.semantic_laws import bound, lam, value
from producers.web_collection14_laws import named_laws, publish, source_functions

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
BASELINE = ROOT/'store/snapshots/30e427bcb8524fe3760881a3a5722c7445f9fdab3d2818a707b8d8508e80c110.json'


def decode(x):
    return struct.unpack('<f', struct.pack('<I', x['F32Bits']))[0] if isinstance(x, dict) else x


def normalize(x, t):
    if t == 'f32':
        try:
            return struct.unpack('<f', struct.pack('<f', x))[0]
        except OverflowError:
            return math.copysign(math.inf, x)
    bits = 64 if t == 'u64' else 32
    x &= (1 << bits)-1
    return x-(1 << bits) if t == 'i32' and x >= 1 << (bits-1) else x


def scalar_key(x, t):
    return struct.unpack('<I', struct.pack('<f', decode(x)))[0] if t == 'f32' else x


def literal_staged(name, args, held_out):
    """Independent eager source pipeline, not an evaluation of proof terms."""
    t = name.rsplit('_', 1)[1]
    xs, seed, k = args
    xs = [decode(x) for x in xs]
    seed, k = decode(seed), decode(k)
    n = lambda x: normalize(x, t)
    values = list(xs)
    if name.startswith('mapped_'):
        mapped = []
        for x in values:
            if not held_out:
                y = n(n(x+seed)*k)
            elif t == 'f32':
                y = n(x+k) if x < seed else n(x-seed)
            else:
                numerator = n(x+seed)
                if k == 0 or (t == 'i32' and numerator == -(1 << 31) and k == -1):
                    y = seed
                else:
                    y = n(abs(numerator)//abs(k) * (-1 if (numerator < 0) != (k < 0) else 1))
            mapped.append(y)
        values = mapped
    if name.startswith('filtered_') or name.startswith('mapped_filtered_'):
        accepted = []
        for x in values:
            if x < (k if held_out else seed):
                accepted.append(x)
        values = accepted
    if '_sum_' in name:
        # Integer addition wraps after every source primitive. No float sum.
        result = 0
        for x in values:
            result = n(result+x)
    else:
        result = seed
        for x in reversed(values):
            result = n(x+n(result*k))
    return {'F32Bits': scalar_key(result, t)} if t == 'f32' and not math.isfinite(result) else result


def frames(t):
    if t == 'f32':
        examples = [([], 0.25, -2.0), ([0.0, -0.0, 1.5, -2.0], 0.25, -2.0),
                    ([65536.0, -0.5, 1.0], -1.0, 0.5),
                    ([{'F32Bits': 0x7fc00000}, {'F32Bits': 0x7f800000}, {'F32Bits': 0xff800000}, -0.0], 0.25, -2.0),
                    ([0.0, -0.0, 1.5, -2.0], {'F32Bits': 0x7fc00000}, 2.0),
                    ([0.0, -0.0, 1.5, -2.0], -0.0, {'F32Bits': 0x7fc00000}),
                    ([0.0, -0.0, 1.0, -1.0], 0.0, -0.0),
                    ([0.0, -0.0, 1.0, -1.0], {'F32Bits': 0x7f800000}, 1.0),
                    ([0.0, -0.0, 1.0, -1.0], 0.0, {'F32Bits': 0xff800000})]
    elif t == 'i32':
        examples = [([], -1, -1), ([-(1 << 31), -1, (1 << 31)-1, 0], 7, 2),
                    ([(1 << 31)-1, 1], -(1 << 31), -1),
                    ([-(1 << 31), -1, 0, 1], 0, -1), ([0, 1, -1], 7, 0)]
    else:
        bits = 64 if t == 'u64' else 32
        maximum = (1 << bits)-1
        examples = [([], maximum, maximum), ([maximum, 0, 1 << (bits-1), 1], 7, 2),
                    ([maximum-1, 17], maximum, maximum), ([0, 1, maximum], 7, 0),
                    ([0, 1, 17, maximum], 7, 1)]
    rng = random.Random(140)
    for length in (17, 31):
        if t == 'f32':
            examples.append(([rng.randint(-8192, 8192)/8 for _ in range(length)],
                             rng.randint(-4096, 4096)/16, rng.randint(-256, 256)/16))
        else:
            bits = 64 if t == 'u64' else 32
            number = lambda: normalize(rng.getrandbits(bits), t)
            examples.append(([number() for _ in range(length)], number(), number()))
    return [[xs, seed, k] for xs, seed, k in examples]


class Collection14Tests(unittest.TestCase):
    def setUp(self):
        self.receipts = []
        archive = os.environ.get('INK_COLLECTION14_EVIDENCE')
        if archive:
            self.directory = Path(archive).resolve()/self._testMethodName
            self.directory.mkdir(parents=True, exist_ok=True)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='ink-collection14-')
            self.directory = Path(self.temporary.name)

    def tearDown(self):
        if os.environ.get('INK_COLLECTION14_EVIDENCE'):
            (self.directory/'commands.json').write_text(json.dumps(self.receipts, indent=2)+'\n')
        elif hasattr(self, 'temporary'):
            self.temporary.cleanup()

    def run_command(self, *args, success=True):
        argv = list(map(str, args))
        result = subprocess.run(argv, capture_output=True, text=True)
        self.receipts.append(dict(argv=argv, exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr))
        if success:
            self.assertEqual(result.returncode, 0, result.stderr)
        return result

    def test_twenty_one_fresh_generic_endpoints_against_pinned_998(self):
        objects = [semantic_entry(candidate) for _, candidate in named_laws()]
        ids = [identity(obj) for obj in objects]
        self.assertEqual(len(ids), 21)
        self.assertEqual(len(set(ids)), 21)
        self.assertEqual(ids, [identity(semantic_entry(candidate)) for _, candidate in named_laws()])
        old = Store(ROOT, BASELINE)
        self.assertEqual(len(old.members()), 998)
        self.assertFalse(set(ids)&set(old.members()))
        endpoints = {(canonical(obj['payload']['from']), canonical(obj['payload']['to'])) for obj in objects}
        for identifier in old.members():
            previous = old.object(identifier)
            if previous['kind'] == 'rewrite' and 'from' in previous['payload']:
                self.assertNotIn((canonical(previous['payload']['from']), canonical(previous['payload']['to'])), endpoints)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_all_admit_and_reuse_default_selection_on_primary_and_held_out_callbacks(self):
        root = self.directory
        before = hashlib.sha256(COMPILER.read_bytes()).hexdigest()
        self.assertEqual(before, '45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        isolated, manifest = publish(root/'isolated')
        previous = Store(ROOT, BASELINE)
        old = Store.publish(root/'prior', [previous.object(i) for i in sorted(previous.members())]); old.rebuild()
        self.assertEqual(old.snapshot_id, previous.snapshot_id)
        combined = Store.publish(root/'combined', [old.object(i) for i in sorted(old.members())]+[isolated.object(i) for i in sorted(isolated.members())]); combined.rebuild()
        source, core = root/'all.ink', root/'all.core.json'
        source.write_text('module Collection14;\n'+'\n'.join(text for _, text in source_functions())+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        admitted = json.loads(self.run_command(COMPILER, 'knowledge-check', core, isolated.root/'view.json').stdout)
        self.assertEqual(set(admitted['entries']), set(manifest['names'].values()))
        (root/'admission.json').write_text(json.dumps(admitted, indent=2)+'\n')
        results, applications, source_variants = [], [], []
        for held_out in (False, True):
            label = 'held-out' if held_out else 'primary'
            functions = source_functions(held_out)
            for index in range(0, len(functions), 5):
                group = functions[index:index+5]
                prefix = root/f'{label}-{index}'
                source, core = prefix.with_suffix('.ink'), prefix.with_suffix('.core.json')
                source.write_text('module Collection14;\n'+'\n'.join(text for _, text in group)+'\n')
                self.run_command(COMPILER, 'emit-core', source, '-o', core)
                original = {f['name']: f['body'] for f in json.loads(core.read_text())['program']['functions']}
                for variant, store in [('prior', old), ('new', combined)]:
                    selection = root/f'{label}-{index}-{variant}.selection.json'
                    planned = self.run_command(sys.executable, ROOT.parent/'planner/plan.py', '--compiler', COMPILER,
                        '--core', core, '--knowledge-root', store.root, '--snapshot', store.data/'snapshot.json',
                        '--budget', 4096, '-o', selection)
                    (root/f'{label}-{index}-{variant}.planner.json').write_text(planned.stdout)
                    package = json.loads(selection.read_text())
                    replay = self.run_command(COMPILER, 'check-selection', core, selection)
                    (root/f'{label}-{index}-{variant}.replay.json').write_text(replay.stdout)
                    selected_core = root/f'{label}-{index}-{variant}.selected.core.json'
                    self.run_command(COMPILER, 'emit-core', source, '--selection', selection, '-o', selected_core)
                    bodies = {f['name']: f['body'] for f in json.loads(selected_core.read_text())['program']['functions']}
                    if variant == 'prior':
                        self.assertEqual(package['applications'], [])
                        self.assertEqual(bodies, original)
                    else:
                        for name, _ in group:
                            used = [a for a in package['applications'] if a['function'] == name]
                            self.assertEqual([a['law'] for a in used], [manifest['names'][name]])
                            self.assertNotEqual(bodies[name], original[name])
                            if name.startswith('mapped_filtered_'):
                                self.assertIn('Let', bodies[name]['Call'][1][2]['Lambda'][1]['Lambda'][1])
                            t = name.rsplit('_', 1)[1]
                            for frame_index, args in enumerate(frames(t)):
                                expected = literal_staged(name, args, held_out)
                                args_file = root/f'{label}-{name}-frame-{frame_index}.json'
                                args_file.write_text(json.dumps(args)+'\n')
                                literal = json.loads(self.run_command(COMPILER, 'run', source, name, args_file).stdout)
                                selected = json.loads(self.run_command(COMPILER, 'run', source, name, args_file, '--selection', selection).stdout)
                                self.assertEqual(scalar_key(literal, t), scalar_key(expected, t), (label, name, args))
                                self.assertEqual(scalar_key(selected, t), scalar_key(literal, t), (label, name, args))
                                results.append(dict(variant=label, function=name, arguments=args, expected=expected, original=literal, selected=selected))
                        applications.extend(dict(variant=label, **a) for a in package['applications'])
                source_variants.append(dict(variant=label, functions=[name for name, _ in group], source=str(source), core=str(core)))
        self.assertEqual(len(applications), 42)
        self.assertEqual(len(results), 318)
        (root/'interpreter-results.json').write_text(json.dumps(results, indent=2)+'\n')
        (root/'reuse.json').write_text(json.dumps(dict(primary_and_held_out_applications=applications, sources=source_variants), indent=2)+'\n')
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), before)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_hash_valid_wrong_filter_branch_and_wrong_mapped_value_rejected(self):
        root = self.directory
        source, core = root/'input.ink', root/'input.core.json'
        source.write_text('module Collection14;\n'+'\n'.join(text for _, text in source_functions())+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        named = dict(named_laws())
        wrong_branch = copy.deepcopy(named['filtered_sum_u32'])
        choose_args = wrong_branch['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']['node']['Op'][1]
        choose_args[1], choose_args[2] = choose_args[2], choose_args[1]
        wrong_mapper = copy.deepcopy(named['mapped_filtered_ordered_affine_fold_f32'])
        shared_apply = wrong_mapper['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']['node']['Op'][1]
        shared_apply[1]['node']['Op'][1][0] = lam(value('F32'), bound(value('F32'), 0))
        for label, candidate in [('opposite-filter-branch', wrong_branch), ('unmapped-predicate-and-value', wrong_mapper)]:
            obj = semantic_entry(candidate)
            store = Store.publish(root/label, [obj])
            view = store.root/'view.json'; view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
            rejected = self.run_command(COMPILER, 'knowledge-check', core, view, success=False)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('semantic normal forms differ', rejected.stderr)
            self.assertNotIn('identity mismatch', rejected.stderr)


if __name__ == '__main__':
    unittest.main()
