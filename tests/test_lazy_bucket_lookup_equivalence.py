"""Exact shared-carrier lookup equality remains independently replayable."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical


class LazyBucketLookupEquivalence(unittest.TestCase):
    def test_portable_exact_source_equality(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/lazy-bucket-lookup-equivalence'
        store = Store(directory)
        roots = list(json.loads((directory / 'store/names.json').read_text()).values())
        with tempfile.TemporaryDirectory() as temp:
            view = Path(temp) / 'view.json'
            view.write_bytes(canonical(store.bundle(roots)))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)['status'], 'checked')


if __name__ == '__main__':
    unittest.main()
