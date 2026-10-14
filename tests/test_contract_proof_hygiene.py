"""Arbitrary source names must survive untrusted proof construction and replay."""
import copy
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge.store import Store, canonical, entry, identity
from producers.action_replacement import call, cons, var
from producers.contract_proofs import MATH, references, state_proof
from producers.point_delta import match


class ContractProofHygiene(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[2]
        cls.compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        cls.temporary = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.directory = Path(cls.temporary.name)
        source = cls.directory / 'source.ink'
        source.write_text('module proof_hygiene;fn identity(x:u32)->u32{return x;}\n')
        cls.core = cls.directory / 'core.json'
        result = subprocess.run([cls.compiler, 'emit-core', source, '-o', cls.core],
                                capture_output=True, text=True, timeout=60)
        if result.returncode:
            raise AssertionError(result.stderr)

    def fixture(self, observed, field_type, names, active):
        objects = {}
        def add(kind, declaration):
            wrapped = {kind: declaration}
            dependencies = references(wrapped)
            pending = list(dependencies)
            while pending:
                for dependency in objects[pending.pop()]['dependencies']:
                    if dependency not in dependencies:
                        dependencies.add(dependency)
                        pending.append(dependency)
            obj = entry('theorem' if kind == 'Theorem' else 'definition', MATH,
                        dict(declaration=wrapped), dependencies,
                        parameters=dict(declaration.get('params', [])),
                        result=declaration.get('result'),
                        conditions=declaration.get('conditions', []))
            ident = identity(obj)
            objects[ident] = obj
            return ident
        datatype = add('Datatype', dict(constructors=[
            dict(name='Empty', fields=[]),
            dict(name='Cell', fields=[field_type, 'SelfType'])]))
        sort = {'Data': datatype}
        empty = cons(datatype, 0, [])
        scrutinee = var('input')
        if observed:
            function = add('Function', dict(params=[['xs', sort]], result=sort,
                recursive=0, body=match(var('xs'), [([], empty),
                    (['head', 'tail'], cons(datatype, 1,
                        [var('head'), {'SelfCall': [var('tail')]}]))])))
            scrutinee = call(function, [var('input')])
        params = {'input': sort, **dict.fromkeys(names, field_type)}
        # Active ambient parameters expose capture, while unused parameters
        # still belong to the kernel's lexical scope and cannot be shadowed.
        left = match(scrutinee, [([], var(names[0])),
                     (['head', 'tail'], var(names[0]))]) if active else match(
            scrutinee, [([], empty), (['head', 'tail'],
                         cons(datatype, 1, [var('head'), var('tail')]))])
        right = var(names[0]) if active else scrutinee
        conditions = [dict(**{'from': match(scrutinee, [([], {'Bool': False}),
            (['head', 'tail'], {'Bool': True})]), 'to': {'Bool': True}})] if observed else []
        proof = state_proof(objects, left, right, params,
                            [(c['from'], c['to'], i) for i, c in enumerate(conditions)])
        theorem = dict(params=list(params.items()), conditions=conditions,
                       **{'from': left, 'to': right}, proof=proof)
        return objects, add, theorem

    def replay(self, objects, theorem):
        with tempfile.TemporaryDirectory(dir=self.directory) as temporary:
            directory = Path(temporary)
            store = Store.publish(directory, objects.values())
            view = directory / 'view.json'
            view.write_bytes(canonical(store.bundle([theorem])))
            return subprocess.run([self.compiler, 'knowledge-check', self.core, view],
                                  capture_output=True, text=True, timeout=60)

    def test_generated_names_cannot_capture_or_shadow_ambient_parameters(self):
        for observed in [False, True]:
            prefix = 'contract_observed_' if observed else 'contract_case_'
            for field_type in ['U64', 'Bool']:
                for stem in ['ordinary_parameter', prefix + '2_0', prefix + '2_1',
                             'delta_hole', 'eq_bound_0_0']:
                    names = [stem, stem + '_1', stem + '_2']
                    for active in [False, True]:
                        with self.subTest(observed=observed, type=field_type, stem=stem, active=active):
                            objects, add, theorem = self.fixture(observed, field_type, names, active)
                            result = self.replay(objects, add('Theorem', theorem))
                            self.assertEqual(result.returncode, 0, result.stderr)

    def test_fresh_names_do_not_authorise_a_rehashed_false_conclusion(self):
        objects, add, theorem = self.fixture(True, 'U64',
            ['delta_hole', 'contract_observed_2_0', 'eq_bound_0_0'], True)
        accepted = self.replay(objects, add('Theorem', theorem))
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        forged = copy.deepcopy(theorem)
        forged['to'] = {'U64': 0}
        rejected = self.replay(objects, add('Theorem', forged))
        self.assertNotEqual(rejected.returncode, 0)
        self.assertNotIn('identity mismatch', rejected.stderr)
        self.assertIn('proof', rejected.stderr)


if __name__ == '__main__':
    unittest.main()
