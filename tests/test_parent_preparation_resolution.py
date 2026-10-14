"""Resolved parent reuse across preparation must replay exact source equations."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry


class PreparationResolution(unittest.TestCase):
    def test_portable_reuse_and_rehashed_dropped_values(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/parent-ordinary-preparation-resolution'
        store = Store(directory)
        names = json.loads((directory / 'store/names.json').read_text())
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            view = d / 'view.json'
            view.write_bytes(canonical(store.bundle(list(names.values()))))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr)
            checkpoint = root / 'knowledge/libraries/proofs/parent-checkpoint-preparation-resolution'
            checkpoint_store = Store(checkpoint)
            checkpoint_names = json.loads((checkpoint / 'store/names.json').read_text())
            view.write_bytes(canonical(checkpoint_store.bundle(list(checkpoint_names.values()))))
            result = subprocess.run([compiler, 'knowledge-check', checkpoint / 'checked-source.json', view], capture_output=True, text=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr)
            lid = names['source/composed_field']
            obj = store.object(lid)
            theorem = dict(copy.deepcopy(obj['payload']), schema=1,
                           semantics=obj['semantics'], dependencies=obj['dependencies'])
            # Demand one exact unfold for a false empty result; source hashing cannot authorize it.
            theorem['to'] = {'sort': theorem['to']['sort'], 'node': 'Nil'}
            theorem['proof'] = 'Unfold'
            bad = semantic_entry(theorem)
            forged = Store.publish(d / 'false', [store.object(i) for i in store.members() if i != lid] + [bad])
            view.write_bytes(canonical(forged.bundle([identity(bad)])))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=180)
            self.assertNotEqual(result.returncode, 0)
            self.assertTrue('exact goal' in result.stderr or 'normal forms differ' in result.stderr, result.stderr)


if __name__ == '__main__':
    unittest.main()
