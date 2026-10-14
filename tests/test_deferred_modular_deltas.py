"""Portable universal delta algebra, with a well-typed forged conclusion."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry


class DeferredModularDeltas(unittest.TestCase):
    def test_portable_composition_and_rehashed_off_by_one(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/deferred-modular-deltas'
        store = Store(directory)
        names = json.loads((directory / 'store/names.json').read_text())
        lid = names['source/modular_delta_composition']
        obj = store.object(lid)
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            view = d / 'view.json'
            view.write_bytes(canonical(store.bundle([lid])))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            theorem = dict(copy.deepcopy(obj['payload']), schema=1,
                           semantics=obj['semantics'], dependencies=obj['dependencies'])
            theorem['to'] = {'sort': theorem['to']['sort'], 'node': {'Op': ['binary:+', [
                theorem['to'], {'sort': theorem['to']['sort'], 'node': {'Word': 1}}
            ]]}}
            bad = semantic_entry(theorem)
            forged = Store.publish(d / 'false', [bad])
            view.write_bytes(canonical(forged.bundle([identity(bad)])))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('normal forms differ', result.stderr)


if __name__ == '__main__':
    unittest.main()
