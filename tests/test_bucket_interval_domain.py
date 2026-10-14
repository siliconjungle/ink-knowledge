"""Bucket arithmetic requires its explicit no-crossing domain premise."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry


class BucketIntervalDomain(unittest.TestCase):
    def test_portable_proof_missing_premise_and_crossing_counterexample(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/bucket-interval-domain'
        store = Store(directory)
        lid = json.loads((directory / 'store/names.json').read_text())['source/fitting_interval_stays_in_bucket']
        obj = store.object(lid)
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            view = d / 'view.json'
            view.write_bytes(canonical(store.bundle([lid])))
            r = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view], capture_output=True, text=True, timeout=120)
            self.assertEqual(r.returncode, 0, r.stderr)
            theorem = dict(copy.deepcopy(obj['payload']), schema=1, semantics=obj['semantics'], dependencies=obj['dependencies'])
            theorem['conditions'] = []
            bad = semantic_entry(theorem)
            forged = Store.publish(d / 'false', [bad])
            view.write_bytes(canonical(forged.bundle([identity(bad)])))
            r = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view], capture_output=True, text=True, timeout=120)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn('unknown bit proof hypothesis', r.stderr)
            args = d / 'args.json'
            args.write_text('[4294967295,2]')
            r = subprocess.run([compiler, 'run', directory / 'checked-source.json', 'same', args, '--core'], capture_output=True, text=True, timeout=120)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn('false', r.stdout)


if __name__ == '__main__':
    unittest.main()
