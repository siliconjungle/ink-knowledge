"""Fixed count equations, real source applications and adversarial RUP replay."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_planner.semantic_search import match, positions
from producers.frozen_laws import index, load
from producers.semantic_laws import value, word
from producers.v8_count_laws import specialize, templates
from producers.v8_integer_laws import bindings

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'knowledge/producers/data/v8-count-laws'
SOURCE = Path(__file__).parent / 'fixtures/v8-count/source.ink'


class CountLaws(unittest.TestCase):
    def setUp(self):
        self.compiler = Path(os.environ.get('INK_COMPILER', ROOT / 'target/debug/ink')).resolve()
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.run_ink('emit-core', SOURCE, '-o', self.directory / 'core.json')

    def tearDown(self):
        self.temporary.cleanup()

    def run_ink(self, *arguments, ok=True):
        result = subprocess.run([str(self.compiler), *map(str, arguments)],
                                capture_output=True, text=True, timeout=180)
        if ok:
            self.assertEqual(result.returncode, 0, result.stderr[-3000:])
        return result

    def save(self, name, value):
        path = self.directory / name
        path.write_bytes(canonical(value))
        return path

    def test_all_eighteen_templates_replay_with_their_exact_statements(self):
        installed = {row['name']: load(DATA, row) for row in index(DATA)}
        self.assertEqual(len(installed), 18)
        self.assertEqual(set(installed), {row['name'] for row in templates()})
        for row in templates():
            claim = installed[row['name']]
            self.assertEqual({key: claim[key] for key in ['params', 'conditions', 'from', 'to']}, row['goal'])
        entries = [semantic_entry(claim) for claim in installed.values()]
        store = Store.publish(self.directory / 'all', entries)
        view = self.save('all.json', store.bundle([identity(entry) for entry in entries]))
        self.run_ink('knowledge-check', self.directory / 'core.json', view)

    def test_real_source_discovery_preserves_wrapping_counts_and_strict_operands(self):
        self.run_ink('emit-semantic', self.directory / 'core.json', '--core', '-o', self.directory / 'subject.json')
        subject = json.loads((self.directory / 'subject.json').read_bytes())
        claims = specialize(subject, {})
        entries = {identity(semantic_entry(claim)): semantic_entry(claim) for _, claim in claims}
        applications = []
        for _, claim in claims:
            for function, body in subject['functions'].items():
                for path, target in positions(body):
                    arguments = {}
                    if match(claim['from'], target, claim['params'], arguments):
                        applications.append(dict(function=function, path=list(path), law=identity(semantic_entry(claim)),
                                                 arguments=arguments, premises=[]))
        self.assertEqual(len(applications), 14)
        store = Store.publish(self.directory / 'empty', [])
        view = ProposalViews(store, entries, self.directory / 'transport').bundle(list(entries))
        selection = self.save('selection.json', dict(schema=1, semantics='ink-evidence-v1',
            input_core_sha256=subject['input_core_sha256'], knowledge=view, applications=applications))
        self.run_ink('check-selection', self.directory / 'core.json', selection)
        counts = [*range(64), 64, 65, 127, 128, 0x80000000, 0xfffffffe, 0xffffffff]
        expected = [dict(pop=1, leading=63-(k & 63), trailing=k & 63) for k in counts]
        calls = [('samples', [counts], expected)]
        for function, inputs in [('zero32', [0, 1, 0x80000000, 0xffffffff]),
                                 ('zero64', [0, 1, 1 << 63, (1 << 64)-1]),
                                 ('zero_signed', [0, 1, -1, -(1 << 31), (1 << 31)-1])]:
            calls.extend((function, [x], x == 0) for x in inputs)
        for selected in [False, True]:
            flags = ['--selection', selection] if selected else []
            for function, inputs, expected in calls:
                args = self.save('args.json', inputs)
                result = self.run_ink('run', self.directory / 'core.json', function, args, '--core', *flags)
                self.assertEqual(json.loads(result.stdout), expected)
            args = self.save('args.json', [0xffffffff])
            result = self.run_ink('run', self.directory / 'core.json', 'strict_k', args, '--core',
                                  '--evaluation-budget', 500, *flags, ok=False)
            self.assertNotEqual(result.returncode, 0)

    def test_rehashed_false_count_proof_still_rejects_after_matching_cnf_hash(self):
        row = next(row for row in index(DATA) if row['name'] == 'u64_popcount_constructed_power')
        claim = copy.deepcopy(load(DATA, row))
        from producers.semantic_laws import var
        u32 = value('U32')
        claim['to'] = bindings([u32], [var(u32, 'k')], lambda arguments: word('U32', 0))
        goal = {key: claim[key] for key in ['params', 'conditions', 'from', 'to']}
        request = self.save('false-goal.json', goal)
        self.run_ink('semantic-bitvector-obligation', self.directory / 'core.json', request, '--core',
                     '--semantics', 'fixed-counts-v5', '--encoding',
                     claim['proof']['BitVector']['certificate'].get('encoding', 'literal-v1'),
                     '-o', self.directory / 'false-cnf.json')
        problem = json.loads((self.directory / 'false-cnf.json').read_bytes())
        claim['proof']['BitVector']['certificate']['problem_sha256'] = problem['sha256']
        entry = semantic_entry(claim)
        store = Store.publish(self.directory / 'false', [entry])
        view = self.save('false.json', store.bundle([identity(entry)]))
        result = self.run_ink('knowledge-check', self.directory / 'core.json', view, ok=False)
        self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main()
