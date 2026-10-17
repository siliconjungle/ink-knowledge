"""Equal projected results need not have equally typed scrutinees."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity
from ink_knowledge.store import entry
from producers.action_replacement import MATH, call, cons, var
from producers.computation_equality import ComputationEquality
from producers.fold_chunks import FoldChunks

ROOT = Path(__file__).resolve().parents[2]
INK = Path(os.environ.get('INK_COMPILER', ROOT/'target/debug/ink')).resolve()


class TypedMatches(unittest.TestCase):
    def test_different_scrutinee_types_can_have_the_same_projected_result(self):
        objects = {}
        def put(declaration, dependencies=()):
            function = declaration.get('Function')
            interface = dict(parameters=dict(function['params']), result=function['result']) if function else {}
            obj = entry('definition', MATH, dict(declaration=declaration), dependencies, **interface)
            key = identity(obj); objects[key] = obj; return key
        first = put({'Datatype': dict(constructors=[dict(name='First', fields=['U64'])])})
        second = put({'Datatype': dict(constructors=[dict(name='Second', fields=['Bool', 'U64'])])})
        a = put({'Function': dict(params=[['x', 'U64']], result={'Data': first}, recursive=None,
            body=cons(first, 0, [var('x')]))}, [first])
        b = put({'Function': dict(params=[['x', 'U64']], result={'Data': second}, recursive=None,
            body=cons(second, 0, [{'Bool': True}, var('x')]))}, [second])
        chunks = FoldChunks(objects, []); chunks.gates.update([a, b])
        left = {'Match': dict(scrutinee=call(a, [var('input')]),
            branches=[dict(bindings=['payload'], body=var('payload'))])}
        right = {'Match': dict(scrutinee=call(b, [var('input')]),
            branches=[dict(bindings=['flag', 'payload'], body=var('payload'))])}
        proof = ComputationEquality(chunks).prove(left, right, {'input': 'U64'})
        theorem = chunks.theorem([['input', 'U64']], left, right, proof)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary); source = folder/'source.ink'
            source.write_text('module typed_matches;fn f(x:u32)->u32{return x;}')
            core = folder/'source.json'
            subprocess.run([INK, 'emit-core', source, '-o', core], check=True, capture_output=True)
            for good in [True, False]:
                root = theorem
                if not good:
                    changed = copy.deepcopy(right)
                    changed['Match']['branches'][0]['body'] = {'U64': 0}
                    root = chunks.theorem([['input', 'U64']], left, changed, proof)
                store = Store.publish(folder/('valid' if good else 'invalid'), list(chunks.objects.values()))
                view = folder/'view.json'; view.write_bytes(canonical(store.bundle([root])))
                result = subprocess.run([INK, 'knowledge-check', core, view], capture_output=True, text=True, timeout=180)
                self.assertEqual(result.returncode == 0, good, result.stderr[-3000:])


if __name__ == '__main__':
    unittest.main()
