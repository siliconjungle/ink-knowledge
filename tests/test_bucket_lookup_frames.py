"""Actual lookup frames replay after exact dependency-context rebinding."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry


class BucketLookupFrames(unittest.TestCase):
    def test_portable_fields_and_rehashed_invalidated_index(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/bucket-lookup-frames'
        store = Store(directory)
        names = json.loads((directory / 'store/names.json').read_text())
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            view = d / 'view.json'
            view.write_bytes(canonical(store.bundle(list(names.values()))))
            r = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view], capture_output=True, text=True, timeout=120)
            self.assertEqual(r.returncode, 0, r.stderr)
            lid = names['source/locate_preserves_valid']
            obj = store.object(lid)
            theorem = dict(copy.deepcopy(obj['payload']), schema=1, semantics=obj['semantics'], dependencies=obj['dependencies'])
            theorem['to'] = {'sort': theorem['to']['sort'], 'node': {'Bool': False}}
            bad = semantic_entry(theorem)
            forged = Store.publish(d / 'false', [store.object(i) for i in store.members() if i != lid] + [bad])
            view.write_bytes(canonical(forged.bundle([identity(bad)])))
            r = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view], capture_output=True, text=True, timeout=120)
            self.assertNotEqual(r.returncode, 0)
            self.assertTrue('exact goal' in r.stderr or 'normal forms differ' in r.stderr, r.stderr)


if __name__ == '__main__':
    unittest.main()
