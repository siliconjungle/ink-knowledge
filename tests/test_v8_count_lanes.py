"""Checked half-word counts: discovery, strictness, boundaries and false proofs."""
import copy
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_planner.semantic_search import match, positions
from producers.frozen_laws import index, load
from producers.semantic_laws import word
from producers.v8_count_lanes import templates, specialize

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'knowledge/producers/data/v8-count-lanes'
SOURCE = Path(__file__).parent / 'fixtures/v8-count-lanes/source.ink'


class CountLanes(unittest.TestCase):
    def setUp(self):
        self.compiler = Path(os.environ.get('INK_COMPILER', ROOT / 'target/debug/ink')).resolve()
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.run_ink('emit-core', SOURCE, '-o', self.directory / 'core.json')
        self.run_ink('emit-semantic', self.directory / 'core.json', '--core', '-o', self.directory / 'subject.json')
        self.subject = json.loads((self.directory / 'subject.json').read_bytes())
        self.claims = {row['name']: load(DATA, row) for row in index(DATA)}

    def tearDown(self):
        self.temporary.cleanup()

    def run_ink(self, *args, ok=True):
        result = subprocess.run([str(self.compiler), *map(str, args)], capture_output=True, text=True, timeout=180)
        if ok:
            self.assertEqual(result.returncode, 0, result.stderr[-3000:])
        return result

    def save(self, name, value):
        path = self.directory / name
        path.write_bytes(canonical(value))
        return path

    def selection(self, label, claims):
        entries = {identity(semantic_entry(c)): semantic_entry(c) for c in claims}
        applications = []
        for claim in claims:
            for function, body in self.subject['functions'].items():
                for path, target in positions(body):
                    args = {}
                    if match(claim['from'], target, claim['params'], args):
                        applications.append(dict(function=function, path=list(path), law=identity(semantic_entry(claim)), arguments=args, premises=[]))
        empty = Store.publish(self.directory / (label + '-empty'), [])
        view = ProposalViews(empty, entries, self.directory / (label + '-transport')).bundle(list(entries))
        package = dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=self.subject['input_core_sha256'], knowledge=view, applications=applications)
        path = self.save(label + '.json', package)
        self.run_ink('check-selection', self.directory / 'core.json', path)
        return path, applications

    def test_all_seven_exact_templates_replay_and_discover_only_u64(self):
        self.assertEqual(len(self.claims), 7)
        catalog = json.loads((ROOT / 'knowledge/ink_knowledge/producer-catalog.json').read_bytes())
        self.assertIn('producers.v8_count_lanes', catalog['modules'])
        self.assertEqual(set(self.claims), {r['name'] for r in templates()})
        entries = []
        for row in templates():
            claim = self.claims[row['name']]
            self.assertEqual({k: claim[k] for k in ['params', 'conditions', 'from', 'to']}, row['goal'])
            entries.append(semantic_entry(claim))
        store = Store.publish(self.directory / 'all', entries)
        view = self.save('all.json', store.bundle([identity(e) for e in entries]))
        self.run_ink('knowledge-check', self.directory / 'core.json', view)
        self.assertEqual(len(specialize(self.subject, {})), 7)
        self.assertEqual(specialize({'functions': {}}, {}), [])
        plain, apps = self.selection('plain', [self.claims[n] for n in ['popcount', 'leading_zeros', 'trailing_zeros']])
        self.assertEqual(len(apps), 9)
        self.assertEqual({a['function'] for a in apps}, {'word', 'samples', 'strict'})

    def test_real_source_all_variants_preserve_boundaries_and_strict_inputs(self):
        rng = random.Random(0x7139)
        words = [0, 1, (1 << 64) - 1, 0xffffffff, 1 << 32, 0xffffffff00000000]
        words += [1 << k for k in range(64)] + [((1 << 64) - 1) ^ (1 << k) for k in range(64)]
        words += [rng.getrandbits(64) for _ in range(64)]
        def expected(x):
            return dict(pop=x.bit_count(), leading=64-x.bit_length(), trailing=64 if x == 0 else (x & -x).bit_length()-1)
        args = self.save('words.json', [words])
        for label, names in [('plain', ['popcount', 'leading_zeros', 'trailing_zeros']),
                             ('zero', ['popcount_zero', 'leading_zeros_zero', 'trailing_zeros_zero_odd']),
                             ('sparse', ['popcount_sparse', 'leading_zeros_zero', 'trailing_zeros_zero_odd'])]:
            selection, _ = self.selection(label, [self.claims[n] for n in names])
            for flags in [[], ['--selection', selection]]:
                result = self.run_ink('run', self.directory / 'core.json', 'samples', args, '--core', *flags)
                self.assertEqual(json.loads(result.stdout), [expected(x) for x in words])
                for x in [0, 1, 1 << 63, (1 << 64) - 1]:
                    strict = self.save('strict.json', [x])
                    result = self.run_ink('run', self.directory / 'core.json', 'strict', strict, '--core', *flags)
                    self.assertEqual(json.loads(result.stdout), expected(x))
                    result = self.run_ink('run', self.directory / 'core.json', 'strict', strict, '--core', '--evaluation-budget', 500, *flags, ok=False)
                    self.assertNotEqual(result.returncode, 0, 'strict input work disappeared')

    def test_rehashed_false_rhs_rejects_with_its_actual_cnf_identity(self):
        for name, original in self.claims.items():
            with self.subTest(name=name):
                claim = copy.deepcopy(original)
                claim['to'] = word('U32', 0)
                goal = self.save(name + '-false-goal.json', {k: claim[k] for k in ['params', 'conditions', 'from', 'to']})
                problem = self.directory / (name + '-false-cnf.json')
                certificate = claim['proof']['BitVector']['certificate']
                self.run_ink('semantic-bitvector-obligation', self.directory / 'core.json', goal, '--core', '--semantics', 'fixed-counts-v5', '--encoding', certificate['encoding'], '-o', problem)
                certificate['problem_sha256'] = json.loads(problem.read_bytes())['sha256']
                entry = semantic_entry(claim)
                store = Store.publish(self.directory / (name + '-false'), [entry])
                view = self.save(name + '-false.json', store.bundle([identity(entry)]))
                self.assertNotEqual(self.run_ink('knowledge-check', self.directory / 'core.json', view, ok=False).returncode, 0)


if __name__ == '__main__':
    unittest.main()
