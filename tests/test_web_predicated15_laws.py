"""Checked generic masked-sum alternatives with explicit planner-policy scope."""
import copy
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.web_predicated15_laws import named_laws, publish, source_functions

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
PIN = '0510381225f45dc33922b2ead3794abd79c190bc3b3cbc34ce41d50e959ed8b1'
BASELINE = ROOT/'store/snapshots'/f'{PIN}.json'


def wrap(x, t):
    bits = 64 if t == 'u64' else 32
    x &= (1 << bits)-1
    return x-(1 << bits) if t == 'i32' and x >= 1 << (bits-1) else x


def eager_source(name, args, held_out):
    """Literal eager stages; independent of semantic proof or selected terms."""
    t = name.rsplit('_', 1)[1]
    xs, seed, k = args
    def mapper(x):
        if held_out:
            return wrap(seed-x, t) if x < seed else wrap(x-seed, t)
        return wrap(wrap(x*3, t)+k, t)
    predicate = (lambda x: x > k) if held_out else (lambda x: x < seed)
    if name.startswith('mapped_filtered_'):
        values = [mapper(x) for x in xs]
        values = [x for x in values if predicate(x)]
    elif name.startswith('filtered_mapped_'):
        values = [x for x in xs if predicate(x)]
        values = [mapper(x) for x in values]
    else:
        values = [x for x in xs if predicate(x)]
    total = 0
    for x in values:
        total = wrap(total+x, t)
    return total


def masked_oracle(name, args, held_out):
    t = name.rsplit('_', 1)[1]
    xs, seed, k = args
    def mapper(x):
        return wrap(seed-x if x < seed else x-seed, t) if held_out else wrap(3*x+k, t)
    predicate = (lambda x: x > k) if held_out else (lambda x: x < seed)
    total = 0
    for x in xs:
        if name.startswith('mapped_filtered_'):
            y = mapper(x)
            contribution = y if predicate(y) else 0
        elif name.startswith('filtered_mapped_'):
            contribution = mapper(x) if predicate(x) else 0
        else:
            contribution = x if predicate(x) else 0
        total = wrap(total+contribution, t)
    return total


def frames(t):
    bits = 64 if t == 'u64' else 32
    low = -(1 << 31) if t == 'i32' else 0
    high = (1 << 31)-1 if t == 'i32' else (1 << bits)-1
    boundary = [low, high, 0, 1, wrap(-1, t), wrap(1 << (bits-1), t)]
    examples = [([], high, high), (boundary, 7, 2), (boundary, low, 0),
                (boundary, high, 1), ([0, 1, 2, 3], 2, wrap(-1, t)),
                ([high, high, high, 1], high, high)]
    rng = random.Random(150)
    for length in (17, 31):
        examples.append(([wrap(rng.getrandbits(bits), t) for _ in range(length)],
                         wrap(rng.getrandbits(bits), t), wrap(rng.getrandbits(bits), t)))
    return [[xs, seed, k] for xs, seed, k in examples]


def operation_names(node):
    result = []
    if isinstance(node, dict):
        if 'Call' in node:
            result.append('call:'+node['Call'][0])
        if 'Method' in node:
            result.append('method:'+node['Method'][1])
        for v in node.values():
            result.extend(operation_names(v))
    elif isinstance(node, list):
        for v in node:
            result.extend(operation_names(v))
    return result


class Predicated15Tests(unittest.TestCase):
    def setUp(self):
        self.receipts = []
        archive = os.environ.get('INK_PREDICATED15_EVIDENCE')
        if archive:
            self.directory = Path(archive).resolve()/self._testMethodName
            self.directory.mkdir(parents=True, exist_ok=True)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix='ink-predicated15-')
            self.directory = Path(self.temporary.name)

    def tearDown(self):
        if os.environ.get('INK_PREDICATED15_EVIDENCE'):
            (self.directory/'commands.json').write_text(json.dumps(self.receipts, indent=2)+'\n')
        else:
            self.temporary.cleanup()

    def run_command(self, *args, success=True):
        argv = list(map(str, args))
        r = subprocess.run(argv, text=True, capture_output=True)
        self.receipts.append(dict(argv=argv, exit_code=r.returncode, stdout=r.stdout, stderr=r.stderr))
        if success:
            self.assertEqual(r.returncode, 0, r.stderr)
        return r

    def test_nine_fresh_generic_endpoints(self):
        objects = [semantic_entry(candidate) for _, candidate in named_laws()]
        ids = [identity(obj) for obj in objects]
        old = Store(ROOT, BASELINE)
        self.assertEqual(len(old.members()), 1031)
        self.assertEqual(len(set(ids)), 9)
        self.assertFalse(set(ids)&set(old.members()))
        endpoints = {(canonical(obj['payload']['from']), canonical(obj['payload']['to'])) for obj in objects}
        for identifier in old.members():
            obj = old.object(identifier)
            if obj['kind'] == 'rewrite' and 'from' in obj['payload']:
                self.assertNotIn((canonical(obj['payload']['from']), canonical(obj['payload']['to'])), endpoints)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_all_nine_objects_admit_independent_of_cost_policy(self):
        source, core = self.directory/'all.ink', self.directory/'all.core.json'
        source.write_text('module Predicated15;\n'+'\n'.join(text for _, text in source_functions())+'\n')
        store, manifest = publish(self.directory/'isolated')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        receipt = json.loads(self.run_command(COMPILER, 'knowledge-check', core, store.root/'view.json').stdout)
        self.assertEqual(set(receipt['entries']), set(manifest['names'].values()))

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    @unittest.skipUnless(os.environ.get('INK_PREDICATED15_COST_MODEL'), 'explicit aggregate cost policy required for target selection')
    def test_admission_isolated_default_replay_and_typed_callback_reuse(self):
        root = self.directory
        before = hashlib.sha256(COMPILER.read_bytes()).hexdigest()
        self.assertEqual(before, '45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        store, manifest = publish(root/'isolated')
        results, applications = [], []
        for held_out in (False, True):
            label = 'held-out' if held_out else 'primary'
            source, core = root/f'{label}.ink', root/f'{label}.core.json'
            source.write_text('module Predicated15;\n'+'\n'.join(text for _, text in source_functions(held_out))+'\n')
            self.run_command(COMPILER, 'emit-core', source, '-o', core)
            admission = self.run_command(COMPILER, 'knowledge-check', core, store.root/'view.json')
            self.assertEqual(set(json.loads(admission.stdout)['entries']), set(manifest['names'].values()))
            selection = root/f'{label}.selection.json'
            self.run_command(sys.executable, ROOT.parent/'planner/plan.py', '--compiler', COMPILER,
                '--core', core, '--knowledge-root', store.root, '--snapshot', store.data/'snapshot.json',
                '--budget', 4096, '-o', selection,
                *(['--cost-model', os.environ['INK_PREDICATED15_COST_MODEL']]
                  if os.environ.get('INK_PREDICATED15_COST_MODEL') else []))
            self.run_command(COMPILER, 'check-selection', core, selection)
            selected = root/f'{label}.selected.core.json'
            self.run_command(COMPILER, 'emit-core', source, '--selection', selection, '-o', selected)
            package = json.loads(selection.read_text())
            bodies = {f['name']: f['body'] for f in json.loads(selected.read_text())['program']['functions']}
            for name, _ in source_functions(held_out):
                used = [a for a in package['applications'] if a['function'] == name]
                self.assertTrue(used, (label, name, 'no predicated alternative selected'))
                self.assertTrue(all(a['law'] in manifest['names'].values() for a in used))
                self.assertIn('call:sum', operation_names(bodies[name]))
                self.assertNotIn('call:foldr', operation_names(bodies[name]))
                self.assertNotIn('method:filter', operation_names(bodies[name]))
                if name.startswith('mapped_filtered_'):
                    self.assertIn('Let', json.dumps(bodies[name]))
                t = name.rsplit('_', 1)[1]
                for i, args in enumerate(frames(t)):
                    expected = eager_source(name, args, held_out)
                    self.assertEqual(masked_oracle(name, args, held_out), expected)
                    path = root/f'{label}-{name}-{i}.args.json'
                    path.write_text(json.dumps(args)+'\n')
                    original = json.loads(self.run_command(COMPILER, 'run', source, name, path).stdout)
                    actual = json.loads(self.run_command(COMPILER, 'run', source, name, path, '--selection', selection).stdout)
                    self.assertEqual(original, expected, (label, name, args))
                    self.assertEqual(actual, expected, (label, name, args))
                    results.append(dict(variant=label, function=name, arguments=args, original=original, selected=actual, expected=expected))
            applications.extend(dict(variant=label, **a) for a in package['applications'])
        self.assertEqual(len(results), 144)
        self.assertEqual(len(applications), 18)
        (root/'interpreter-results.json').write_text(json.dumps(results, indent=2)+'\n')
        (root/'selected-applications.json').write_text(json.dumps(applications, indent=2)+'\n')
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(), before)

    @unittest.skipUnless(COMPILER.is_file(), 'frozen compiler required')
    def test_hash_valid_false_mask_and_mapper_rejected(self):
        root = self.directory
        source, core = root/'input.ink', root/'input.core.json'
        source.write_text('module Predicated15;\n'+'\n'.join(text for _, text in source_functions())+'\n')
        self.run_command(COMPILER, 'emit-core', source, '-o', core)
        candidates = dict(named_laws())
        branch = copy.deepcopy(candidates['filtered_predicated_sum_u32'])
        args = branch['to']['node']['Op'][1][0]['node']['Op'][1][1]['node']['Lambda']['node']['Op'][1]
        args[1], args[2] = args[2], args[1]
        mapper = copy.deepcopy(candidates['filtered_mapped_predicated_sum_u32'])
        args = mapper['to']['node']['Op'][1][0]['node']['Op'][1][1]['node']['Lambda']['node']['Op'][1]
        args[1] = args[1]['node']['Op'][1][1]
        for label, candidate in [('inverted-mask', branch), ('unmapped-accepted-value', mapper)]:
            obj = semantic_entry(candidate)
            store = Store.publish(root/label, [obj])
            view = store.root/'view.json'
            view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
            r = self.run_command(COMPILER, 'knowledge-check', core, view, success=False)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn('semantic normal forms differ', r.stderr)
            self.assertNotIn('identity mismatch', r.stderr)


if __name__ == '__main__':
    unittest.main()
