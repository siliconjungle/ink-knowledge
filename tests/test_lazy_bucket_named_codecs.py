"""Both actual named carrier codecs require complete source replay."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical


class LazyBucketNamedCodecs(unittest.TestCase):
    def test_roundtrips_and_dropped_validity_rejection(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            for name in ['lazy-bucket-named-codec', 'lazy-bucket-named-reverse-codec']:
                directory = root / 'knowledge/libraries/proofs' / name
                store = Store(directory)
                roots = list(json.loads((directory / 'store/names.json').read_text()).values())
                view = d / 'view.json'
                view.write_bytes(canonical(store.bundle(roots)))
                result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view], capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode, 0, result.stderr)
            source = root / 'examples/crdts/lazy_bucket_named_transport.ink'
            changed = source.read_text().replace('valid:index.valid', 'valid:false')
            changed = changed.replace('../../knowledge/libraries/', str(root / 'knowledge/libraries') + '/')
            self.assertNotEqual(changed, source.read_text())
            bad = d / 'false.ink'
            bad.write_text(changed)
            core = d / 'core.json'
            result = subprocess.run([compiler, 'emit-core', bad, '-o', core], capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            result = subprocess.run([os.environ.get('INK_PYTHON', 'python3'), root / 'tools/source_pair_equality.py',
                '--compiler', compiler, '--core', core, '--left', 'roundtrip', '--right', 'unchanged', '-o', d / 'proof'],
                capture_output=True, text=True, timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse((d / 'proof').exists())


if __name__ == '__main__':
    unittest.main()
