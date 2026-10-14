"""Bucket partition arithmetic carries an explicit strict-interior premise."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry


class BucketPartitionDomain(unittest.TestCase):
    def test_portable_partition_domain_and_missing_premise(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/bucket-partition-domain'
        store = Store(directory)
        lid = json.loads((directory / 'store/names.json').read_text())['source/interior_partition_preserves_buckets']
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
            args.write_text('[1,10,1]')
            r = subprocess.run([compiler, 'run', directory / 'checked-source.json', 'preserved', args, '--core'], capture_output=True, text=True, timeout=120)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn('false', r.stdout)


if __name__ == '__main__':
    unittest.main()
