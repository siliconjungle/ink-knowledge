"""Alpha matching proposes ordinary proofs, including branching induction."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity
from ink_knowledge.store import entry
from producers.action_replacement import MATH, call, var
from producers.definition_correspondence import DefinitionCorrespondence
from producers.fold_chunks import FoldChunks

ROOT = Path(__file__).resolve().parents[2]
COMPILER = Path(os.environ.get('INK_COMPILER', ROOT/'target/debug/ink')).resolve()


def examples(different_constant=False):
    objects = {}
    def put(declaration, dependencies=()):
        signature = declaration.get('Function')
        interface = dict(parameters=dict(signature['params']), result=signature['result']) if signature else {}
        obj = entry('definition', MATH, {'declaration': declaration}, dependencies, **interface)
        key = identity(obj); objects[key] = obj
        return key
    tree = put({'Datatype': {'constructors': [dict(name='Tip', fields=['U64']),
        dict(name='Fork', fields=['SelfType', 'SelfType'])]}})
    helpers, functions = [], []
    for version in range(2):
        name = 'value_'+str(version)
        helper = put({'Function': dict(params=[[name, 'U64']], result='U64', recursive=None,
            body={'Binary': dict(op='+', left=var(name), right={'U64': 2 if different_constant and version else 1})})})
        helpers.append(helper)
        root, offset, leaf, left, right = [n+str(version) for n in ['root', 'offset', 'leaf', 'left', 'right']]
        body = {'Match': dict(scrutinee=var(root), branches=[
            dict(bindings=[leaf], body={'Binary': dict(op='+', left=call(helper, [var(leaf)]), right=var(offset))}),
            dict(bindings=[left, right], body={'Binary': dict(op='+',
                left={'SelfCall': [var(left), var(offset)]}, right={'SelfCall': [var(right), var(offset)]})})])}
        functions.append(put({'Function': dict(params=[[root, {'Data': tree}], [offset, 'U64']],
            result='U64', recursive=0, body=body)}, [tree, helper]))
    return objects, helpers, functions


class Correspondence(unittest.TestCase):
    def test_unchanged_large_bodies_keep_compact_checked_equations(self):
        objects = {}
        functions = []
        for version in range(2):
            value, flag = 'value_'+str(version), 'flag_'+str(version)
            body = var(value)
            for index in range(8):
                body = {'If': dict(condition=var(flag), on_true=body,
                    on_false={'Binary': dict(op='+', left=body, right={'U64': index})})}
            function = dict(params=[[value, 'U64'], [flag, 'Bool']], result='U64',
                            recursive=None, body=body)
            obj = entry('definition', MATH, {'declaration': {'Function': function}},
                        parameters=dict(function['params']), result='U64')
            key = identity(obj); objects[key] = obj; functions.append(key)
        chunks = FoldChunks(objects, [])
        theorem = DefinitionCorrespondence(chunks).bridge(*functions)
        proof = chunks.objects[theorem]['payload']['declaration']['Theorem']['proof']
        self.assertIn('Convert', proof)
        self.assertLess(len(canonical(proof)), 600)
        self.assertLess(chunks.work, 500)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder/'source.ink'
            source.write_text('module compact_correspondence; pub fn f(x:u32)->u32{return x;}')
            core = folder/'core.json'
            emitted = subprocess.run([COMPILER, 'emit-core', source, '-o', core],
                                     capture_output=True, text=True, timeout=120)
            self.assertEqual(emitted.returncode, 0, emitted.stderr)
            store = Store.publish(folder/'proofs', list(chunks.objects.values()))
            view = folder/'view.json'; view.write_bytes(canonical(store.bundle([theorem])))
            checked = subprocess.run([COMPILER, 'knowledge-check', core, view],
                                     capture_output=True, text=True, timeout=120)
            self.assertEqual(checked.returncode, 0, checked.stderr)

    def test_two_recursive_children_and_generalized_parameter_replay(self):
        objects, helpers, functions = examples()
        chunks = FoldChunks(objects, [])
        bridge = DefinitionCorrespondence(chunks)
        theorem = bridge.bridge(*functions)
        self.assertEqual(bridge.bridge(*functions), theorem)
        self.assertIn(tuple(helpers), bridge.cache)
        proof = chunks.objects[theorem]['payload']['declaration']['Theorem']['proof']['GeneralizedInduction']
        self.assertEqual(proof['generalize'], ['correspondence_arg_1'])
        with tempfile.TemporaryDirectory() as temporary:
            d = Path(temporary)
            source = d/'source.ink'; source.write_text('module correspondence; pub fn f(x:u32)->u32{return x;}')
            result = subprocess.run([str(COMPILER), 'emit-core', str(source), '-o', str(d/'core.json')],
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            for valid in [True, False]:
                imported = dict(chunks.objects)
                root = theorem
                if not valid:
                    bad = copy.deepcopy(imported[theorem])
                    bad['payload']['declaration']['Theorem']['to'] = {'U64': 0}
                    root = identity(bad); imported[root] = bad
                store = Store.publish(d/('valid' if valid else 'invalid'), list(imported.values()))
                view = d/'view.json'; view.write_bytes(canonical(store.bundle([root])))
                result = subprocess.run([str(COMPILER), 'knowledge-check', str(d/'core.json'), str(view)],
                                        capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode == 0, valid, result.stderr)

    def test_different_body_and_incompatible_signatures_decline(self):
        objects, _, functions = examples(different_constant=True)
        with self.assertRaisesRegex(ValueError, 'differs'):
            DefinitionCorrespondence(FoldChunks(objects, [])).bridge(*functions)
        objects, _, functions = examples()
        changed = copy.deepcopy(objects[functions[1]])
        changed['payload']['declaration']['Function']['recursive'] = None
        key = identity(changed); objects[key] = changed
        with self.assertRaisesRegex(ValueError, 'signature'):
            DefinitionCorrespondence(FoldChunks(objects, [])).bridge(functions[0], key)

    def test_mismatched_call_arity_declines(self):
        objects, _, functions = examples()
        author = DefinitionCorrespondence(FoldChunks(objects, []))
        with self.assertRaisesRegex(ValueError, 'arity'):
            author.terms(call(functions[0], [var('tree')]),
                         call(functions[1], [var('tree'), {'U64': 0}]),
                         {}, {}, {}, 0)


if __name__ == '__main__':
    unittest.main()
