"""Generic fold admission, checked specialization, bounded search and oracles."""
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
from producers.beta_specialization15 import derive
from producers.semantic_laws import bound
from producers.web_fold16_laws import named_laws, publish, source_functions

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
PIN = '57bbee1835725fd3af939cf11e3dda25ac51e12001fde0f006aeb64bb9ab2378'
BASELINE = ROOT/'store/snapshots'/f'{PIN}.json'


def alpha_endpoints(candidate):
    """Canonicalize free-variable spelling, retaining every sort and binder."""
    names = {}
    def walk(node):
        if isinstance(node, dict):
            if set(node) == {'Free'}:
                name = node['Free']
                if name not in names:
                    names[name] = 'v'+str(len(names))
                return {'Free': names[name]}
            return {k: walk(node[k]) for k in sorted(node)}
        if isinstance(node, list):
            return [walk(x) for x in node]
        return node
    return canonical(walk([candidate['from'], candidate['to']]))


def normalize(x, t):
    if t == 'f32':
        try:
            return struct.unpack('<f', struct.pack('<f', x))[0]
        except OverflowError:
            return math.copysign(math.inf, x)
    bits = 64 if t == 'u64' else 32
    x &= (1 << bits)-1
    return x-(1 << 32) if t == 'i32' and x >= 1 << 31 else x


def decode(x):
    return struct.unpack('<f', struct.pack('<I', x['F32Bits']))[0] if isinstance(x, dict) else x


def result_key(x, t):
    return struct.unpack('<I', struct.pack('<f', decode(x)))[0] if t == 'f32' else x


def eager_oracle(name, arguments, held_out, backwards=True):
    """Allocate literal source stages, then execute the ordered recurrence."""
    t = name.rsplit('_', 1)[1]
    xs, seed, k = arguments
    xs, seed, k = [decode(x) for x in xs], decode(seed), decode(k)
    n = lambda x: normalize(x, t)
    f = (lambda x: n(seed-x) if x < seed else n(x-seed)) if held_out else (lambda x: n(n(x*3)+k))
    p = (lambda x: x > k) if held_out else (lambda x: x < seed)
    if name.startswith('mapped_filtered_'):
        values = [f(x) for x in xs]
        values = [x for x in values if p(x)]
    elif name.startswith('filtered_mapped_'):
        values = [x for x in xs if p(x)]
        values = [f(x) for x in values]
    else:
        values = [x for x in xs if p(x)]
    a, yes, no = seed, 0, 0
    for x in reversed(values) if backwards else values:
        condition = a < seed if held_out else x < k
        yes += int(condition); no += int(not condition)
        if held_out:
            a = n(x-a) if condition else n(x+a)
        else:
            a = n(x+n(a*k)) if condition else n(x-a)
    return a, dict(accepted=len(values), reducer_true=yes, reducer_false=no)


def fused_oracle(name, arguments, held_out):
    """Independent one-pass traversal; no eager stage list or proof terms."""
    t = name.rsplit('_', 1)[1]
    xs, seed, k = arguments
    seed, k = decode(seed), decode(k)
    a = seed
    for raw in reversed(xs):
        x = decode(raw)
        if name.startswith('mapped_filtered_'):
            x = normalize((seed-x if x < seed else x-seed) if held_out else normalize(x*3, t)+k, t)
        accepted = x > k if held_out else x < seed
        if not accepted:
            continue
        if name.startswith('filtered_mapped_'):
            x = normalize((seed-x if x < seed else x-seed) if held_out else normalize(x*3, t)+k, t)
        if held_out:
            a = normalize(x-a if a < seed else x+a, t)
        else:
            a = normalize(x+normalize(a*k, t) if x < k else x-a, t)
    return a


def frames(t):
    if t == 'f32':
        examples = [([], 0.25, -2.0), ([0.0, -0.0, 1.5, -2.0], 2.0, 1.0),
            ([65536.0, -0.5, 1.0], -1.0, 0.5),
            ([{'F32Bits': 0x7fc00000}, {'F32Bits': 0x7f800000}, {'F32Bits': 0xff800000}, -0.0], 2.0, 1.0),
            ([0.0, -0.0, 1.5, -2.0], {'F32Bits': 0x7fc00000}, 2.0),
            ([0.0, -0.0, 1.5, -2.0], 2.0, {'F32Bits': 0x7fc00000}),
            ([0.0, -0.0, 1.0, -1.0], -0.0, {'F32Bits': 0x7f800000})]
    else:
        bits = 64 if t == 'u64' else 32
        low, high = (-(1 << 31), (1 << 31)-1) if t == 'i32' else (0, (1 << bits)-1)
        examples = [([], high, high), ([low, high, 0, 1, normalize(-1, t)], 7, 2),
                    ([high, high, 1], low, normalize(-1, t)), ([1, 2, 3, 4, 5], 7, 3)]
    rng = random.Random(16)
    for size in (17, 31):
        if t == 'f32':
            xs = [rng.randrange(-256, 256)/8 for _ in range(size)]
            examples.append((xs, 17.0, 3.0))
        else:
            bits = 64 if t == 'u64' else 32
            examples.append(([normalize(rng.getrandbits(bits), t) for _ in range(size)],
                             normalize(rng.getrandbits(bits), t), normalize(rng.getrandbits(bits), t)))
    return [[xs, seed, k] for xs, seed, k in examples]


class Fold16Tests(unittest.TestCase):
    def setUp(self):
        self.commands = []
        archive = os.environ.get('INK_FOLD16_EVIDENCE')
        if archive:
            self.directory = Path(archive).resolve()/self._testMethodName
            self.directory.mkdir(parents=True, exist_ok=True)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='ink-fold16-')
            self.directory = Path(self.temporary.name)

    def tearDown(self):
        if os.environ.get('INK_FOLD16_EVIDENCE'):
            (self.directory/'commands.json').write_text(json.dumps(self.commands, indent=2)+'\n')
        else:
            self.temporary.cleanup()

    def run_command(self, *args, success=True):
        argv = list(map(str, args))
        r = subprocess.run(argv, capture_output=True, text=True)
        self.commands.append(dict(argv=argv, exit_code=r.returncode, stdout=r.stdout, stderr=r.stderr))
        if success:
            self.assertEqual(r.returncode, 0, r.stderr)
        return r

    def test_fresh_alpha_endpoints_against_immutable_1089(self):
        candidates = named_laws()
        ids = {identity(semantic_entry(v)) for _, v in candidates}
        self.assertEqual(len(ids), 12)
        old = Store(ROOT, BASELINE)
        self.assertEqual(len(old.members()), 1089)
        self.assertFalse(ids & set(old.members()))
        endpoints = {alpha_endpoints(v) for _, v in candidates}
        for identifier in old.members():
            p = old.object(identifier)['payload']
            if 'from' in p and 'node' in p['from']:
                self.assertNotIn(alpha_endpoints(p), endpoints)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_admit_compose_bounded_select_reify_all_types_and_callback_holdouts(self):
        before = hashlib.sha256(COMPILER.read_bytes()).hexdigest()
        self.assertEqual(before, '45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        generic = named_laws()
        isolated, manifest = publish(self.directory/'generic')
        results, scopes = [], []
        for held_out in (False, True):
            label = 'held-out' if held_out else 'primary'
            source = self.directory/(label+'.ink')
            core = self.directory/(label+'.core.json')
            subject_path = self.directory/(label+'.semantic.json')
            source.write_text('module Fold16;\n'+'\n'.join(text for _, text in source_functions(held_out))+'\n')
            self.run_command(COMPILER, 'emit-core', source, '-o', core)
            self.run_command(COMPILER, 'knowledge-check', core, isolated.root/'view.json')
            self.run_command(COMPILER, 'emit-semantic', core, '--core', '-o', subject_path)
            subject = json.loads(subject_path.read_text())
            derived = derive(subject, generic)
            # All dependencies are just the twelve independently admitted generic
            # proofs. Never copy the canonical store or its observations.
            store = Store.publish(self.directory/(label+'-certificates'), [semantic_entry(v) for _, v in generic+derived])
            store.rebuild()
            roots = [identity(semantic_entry(v)) for _, v in derived]
            view = self.directory/(label+'-view.json')
            view.write_bytes(canonical(store.bundle(roots))+b'\n')
            self.run_command(COMPILER, 'knowledge-check', core, view)
            selection = self.directory/(label+'-selection.json')
            # Bounded per-function discovery avoids combinatorial whole-module
            # beam exhaustion. The union is independently replayed on the exact
            # original full module below; no forced law application is inserted.
            applications, planner_receipts = [], []
            for name, text in source_functions(held_out):
                unit_source = self.directory/f'{label}-{name}.ink'
                unit_core = self.directory/f'{label}-{name}.core.json'
                unit_selection = self.directory/f'{label}-{name}.selection.json'
                unit_source.write_text('module Fold16Unit;\n'+text+'\n')
                self.run_command(COMPILER, 'emit-core', unit_source, '-o', unit_core)
                planned = self.run_command(sys.executable, ROOT.parent/'planner/plan.py', '--compiler', COMPILER,
                    '--core', unit_core, '--knowledge-root', store.root, '--snapshot', store.data/'snapshot.json',
                    '--budget', 128, '-o', unit_selection)
                planner_receipts.append(json.loads(planned.stdout))
                applications.extend(json.loads(unit_selection.read_text())['applications'])
            combined = dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=subject['input_core_sha256'],
                            knowledge=store.bundle(roots), applications=applications)
            selection.write_text(json.dumps(combined, indent=2)+'\n')
            replay = self.run_command(COMPILER, 'check-selection', core, selection)
            selected = self.directory/(label+'-selected.core.json')
            self.run_command(COMPILER, 'emit-core', source, '--selection', selection, '-o', selected)
            semantic_selected = self.directory/(label+'-selected.semantic.json')
            self.run_command(COMPILER, 'emit-semantic', selected, '--core', '-o', semantic_selected)
            package = json.loads(selection.read_text())
            selected_terms = json.loads(semantic_selected.read_text())['functions']
            selected_bodies = {f['name']: f['body'] for f in json.loads(selected.read_text())['program']['functions']}
            derived_by_id = {identity(semantic_entry(v)): v for _, v in derived}
            for name, _ in source_functions(held_out):
                used = [a for a in package['applications'] if a['function'] == name]
                self.assertEqual(len(used), 1, (label, name, used))
                candidate = derived_by_id[used[0]['law']]
                self.assertEqual(selected_terms[name], candidate['to'])
                self.assertNotIn('method:map', json.dumps(selected_terms[name]))
                self.assertNotIn('method:filter', json.dumps(selected_terms[name]))
                self.assertNotIn('apply', json.dumps(selected_terms[name]))
                self.assertNotIn('Let', json.dumps(selected_bodies[name]))
                t = name.rsplit('_', 1)[1]
                for index, args in enumerate(frames(t)):
                    expected, branches = eager_oracle(name, args, held_out)
                    fused = fused_oracle(name, args, held_out)
                    if t == 'f32' and math.isnan(expected):
                        self.assertTrue(math.isnan(fused))
                    else:
                        self.assertEqual(result_key(expected, t), result_key(fused, t))
                    path = self.directory/f'{label}-{name}-{index}.args.json'
                    path.write_text(json.dumps(args)+'\n')
                    original = json.loads(self.run_command(COMPILER, 'run', source, name, path).stdout)
                    actual = json.loads(self.run_command(COMPILER, 'run', source, name, path, '--selection', selection).stdout)
                    self.assertEqual(result_key(original, t), result_key(actual, t), (label, name, args))
                    if t == 'f32' and math.isnan(expected):
                        self.assertTrue(math.isnan(decode(actual)))
                    else:
                        self.assertEqual(result_key(actual, t), result_key(expected, t), (label, name, args))
                    results.append(dict(variant=label, function=name, arguments=args,
                        expected=({'F32Bits': result_key(expected, t)} if t == 'f32' and not math.isfinite(expected) else expected),
                        original=original, selected=actual, branches=branches))
            scopes.append(dict(variant=label, generic_laws=12, certificates=len(derived),
                selections=planner_receipts, replay=json.loads(replay.stdout), applications=package['applications']))
        self.assertEqual(len(results), 162)
        # Explicitly prove the fixtures distinguish right from left traversal.
        args = [[1, 2, 3, 4, 5], 7, 3]
        right = eager_oracle('filtered_arbitrary_fold_u32', args, False)[0]
        left = eager_oracle('filtered_arbitrary_fold_u32', args, False, backwards=False)[0]
        self.assertNotEqual(right, left)
        (self.directory/'ordered-counterexample.json').write_text(json.dumps(dict(arguments=args, right=right, left=left))+'\n')
        (self.directory/'interpreter-results.json').write_text(json.dumps(results, indent=2)+'\n')
        (self.directory/'scope.json').write_text(json.dumps(scopes, indent=2)+'\n')
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), before)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_hash_valid_swapped_filter_and_accumulator_controls_rejected(self):
        source, core = self.directory/'input.ink', self.directory/'input.core.json'
        source.write_text('module FalseFold16;\n'+'\n'.join(t for _, t in source_functions())+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        good = dict(named_laws())['filtered_arbitrary_fold_u32']
        branch = copy.deepcopy(good)
        args = branch['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']['node']['Op'][1]
        args[1], args[2] = args[2], args[1]
        accumulator = copy.deepcopy(good)
        args = accumulator['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']['node']['Op'][1]
        args[1]['node']['Op'][1][1] = bound({'Value':'U32'}, 1)
        for label, candidate in [('inverted-filter', branch), ('head-instead-of-accumulator', accumulator)]:
            obj = semantic_entry(candidate)
            store = Store.publish(self.directory/label, [obj])
            view = store.root/'view.json'
            view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
            r = self.run_command(COMPILER, 'knowledge-check', core, view, success=False)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn('semantic normal forms differ', r.stderr)
            self.assertNotIn('identity mismatch', r.stderr)


if __name__ == '__main__':
    unittest.main()
