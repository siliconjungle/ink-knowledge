"""The actual cursor fast branch requires validated membership."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical


class CursorHintHit(unittest.TestCase):
    def test_portable_guarded_proof_and_observable_counterexample(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/cursor-hint-hit'
        store = Store(directory)
        roots = list(json.loads((directory / 'store/names.json').read_text()).values())
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            view = d / 'view.json'
            view.write_bytes(canonical(store.bundle(roots)))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view], capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            source = root / 'examples/crdts/cursor_hint_hit.ink'
            module = d / 'source.mjs'
            result = subprocess.run([compiler, 'build', source, '--target', 'javascript', '-o', module], capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            script = d / 'check.mjs'
            script.write_text("import assert from 'node:assert/strict';import {call} from './source.mjs';\n"
                              "assert.deepEqual(call('compared',[1]),{hit:true,fast:7,selected:7});\n"
                              "assert.deepEqual(call('compared',[0]),{hit:false,fast:0,selected:7});\n")
            result = subprocess.run(['node', script], capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == '__main__':
    unittest.main()
