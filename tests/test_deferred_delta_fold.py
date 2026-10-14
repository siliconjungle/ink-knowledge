"""Universal bulk-delta laws need checked arbitrary-list induction."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical


class DeferredDeltaFold(unittest.TestCase):
    def test_portable_replay_and_changed_bulk_conclusion(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        source = root / 'knowledge/libraries/deferred-delta-laws.ink'
        directory = root / 'knowledge/libraries/proofs/deferred-delta-fold'
        store = Store(directory)
        names = json.loads((directory / 'store/names.json').read_text())
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            view = d / 'view.json'
            view.write_bytes(canonical(store.bundle(list(names.values()))))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            original = source.read_text()
            changed = original.replace(
                '== total-foldl(xs,0,fn(d,value)=>value+d.old)+foldl(xs,0,fn(d,value)=>value+d.new);',
                '== total-foldl(xs,0,fn(d,value)=>value+d.old)+foldl(xs,0,fn(d,value)=>value+d.new)+1;')
            self.assertNotEqual(changed, original)
            bad = d / 'false.ink'
            bad.write_text(changed)
            result = subprocess.run([compiler, 'emit-laws', bad, '-o', d / 'false.json'],
                                    capture_output=True, text=True, timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('law bulk_deltas:', result.stderr)


if __name__ == '__main__':
    unittest.main()
