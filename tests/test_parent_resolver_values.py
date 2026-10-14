"""Actual resolver values need a portable source-bound equality closure."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry


class ParentResolverValues(unittest.TestCase):
    def test_portable_values_and_rehashed_dropped_parents(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/parent-resolver-values'
        store = Store(directory)
        names = json.loads((directory / 'store/names.json').read_text())
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            view = d / 'view.json'
            view.write_bytes(canonical(store.bundle(list(names.values()))))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            lid = names['source/ordinary_resolved_values']
            obj = store.object(lid)
            theorem = dict(copy.deepcopy(obj['payload']), schema=1,
                           semantics=obj['semantics'], dependencies=obj['dependencies'])
            theorem['to'] = {'sort': theorem['to']['sort'], 'node': 'Nil'}
            bad = semantic_entry(theorem)
            forged = Store.publish(d / 'false', [store.object(i) for i in store.members() if i != lid] + [bad])
            view.write_bytes(canonical(forged.bundle([identity(bad)])))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertTrue('exact goal' in result.stderr or 'normal forms differ' in result.stderr, result.stderr)


if __name__ == '__main__':
    unittest.main()
