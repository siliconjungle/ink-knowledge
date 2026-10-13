"""Guarded variants of conditional laws are ordinary kernel-checked laws."""
import copy, json, os, subprocess, tempfile, unittest
from pathlib import Path
from ink_knowledge import Store, canonical
from ink_knowledge.guarded_laws import eligible, generate, guard, guard_condition
ROOT = Path(__file__).resolve().parents[2]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT / 'target/debug/ink'))
LAWS = '''module guarded;
law pick_true(flag: Bool, a: u32, b: u32) {
    requires flag;
    choose(flag, a, b) == a;
    proof by normalize;
}
law small_pair(x: u32, y: u32) {
    requires x < 16;
    requires y > 3;
    choose(x < 16 && y > 3, x * x, y) == x * x;
    proof by normalize;
}
law constant_premise(x: u32) {
    requires 1 < 2;
    x + 0 == x;
    proof by normalize;
}
'''
PROGRAM = 'module subject;\npub fn f(x:u32)->u32{return x;}\n'


def run(*command):
    r = subprocess.run([str(c) for c in command], capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


class Guarded(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(); d = Path(cls.tmp.name)
        (d / 'laws.ink').write_text(LAWS); (d / 'p.ink').write_text(PROGRAM)
        code, out = run(COMPILER, 'emit-laws', d / 'laws.ink', '-o', d / 'laws.json')
        assert code == 0, out
        receipt = json.loads(out.strip().splitlines()[-1])
        cls.names = receipt['names']
        cls.objects = json.loads((d / 'laws.json').read_text())['objects']
        code, out = run(COMPILER, 'emit-core', d / 'p.ink', '-o', d / 'core.json')
        assert code == 0, out
        cls.dir = d

    @classmethod
    def tearDownClass(cls): cls.tmp.cleanup()

    def admits(self, extra, roots):
        d = Path(tempfile.mkdtemp(dir=self.dir))
        store = Store.publish(d / 'knowledge', list(self.objects.values()) + list(extra.values()))
        (d / 'view.json').write_bytes(canonical(store.bundle(sorted(roots))) + b'\n')
        return run(COMPILER, 'knowledge-check', self.dir / 'core.json', d / 'view.json')

    def test_only_data_dependent_bool_premises_are_guarded(self):
        self.assertTrue(eligible(self.objects[self.names['pick_true']]))
        self.assertTrue(eligible(self.objects[self.names['small_pair']]))
        self.assertFalse(eligible(self.objects[self.names['constant_premise']]))

    def test_guarded_variants_check_and_keep_the_original_on_failure(self):
        derived = generate(self.objects)
        self.assertEqual(len(derived), 2)
        for ident, entry in derived.items():
            law = entry['payload']
            self.assertEqual(law['conditions'], [])
            self.assertIsNotNone(guard_condition(law))
            # The else branch is the unchanged left side.
            self.assertEqual(law['to']['node']['Op'][1][2], law['from'])
        code, out = self.admits(derived, derived)
        self.assertEqual(code, 0, out)

    def test_a_guard_with_swapped_branches_is_rejected(self):
        ident = self.names['pick_true']
        entry = copy.deepcopy(guard(ident, self.objects[ident]))
        node = entry['payload']['to']['node']['Op'][1]
        node[1], node[2] = node[2], node[1]
        from ink_knowledge.store import identity, semantic_entry
        law = {k: v for k, v in entry['payload'].items()}
        bad = semantic_entry(dict(schema=1, semantics=entry['semantics'], dependencies=entry['dependencies'], **law))
        code, out = self.admits({identity(bad): bad}, [identity(bad)])
        self.assertNotEqual(code, 0, out)


if __name__ == '__main__':
    unittest.main()
