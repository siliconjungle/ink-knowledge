"""Source-bound adjustment frames retain their exact structural scope."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry


class DeferredAdjustmentFrames(unittest.TestCase):
    def test_actual_adjusted_and_flush_closures(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        for name in ['deferred-adjusted-source-frames', 'deferred-flush-frames']:
            directory = root / 'knowledge/libraries/proofs' / name
            store = Store(directory)
            names = json.loads((directory / 'store/names.json').read_text())
            with tempfile.TemporaryDirectory() as temp:
                view = Path(temp) / 'view.json'
                view.write_bytes(canonical(store.bundle(list(names.values()))))
                result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view], capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode, 0, name + result.stderr)

    def test_portable_frames_and_rehashed_false_root(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/deferred-adjustment-frames'
        store = Store(directory)
        names = json.loads((directory / 'store/names.json').read_text())
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            view = d / 'view.json'
            view.write_bytes(canonical(store.bundle(list(names.values()))))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            lid = names['source/adjust_preserves_tree_root']
            obj = store.object(lid)
            theorem = dict(copy.deepcopy(obj['payload']), schema=1,
                           semantics=obj['semantics'], dependencies=obj['dependencies'])
            theorem['to'] = {'sort': theorem['to']['sort'], 'node': {'Word': 0}}
            bad = semantic_entry(theorem)
            forged = Store.publish(d / 'false', [store.object(i) for i in store.members() if i != lid] + [bad])
            view.write_bytes(canonical(forged.bundle([identity(bad)])))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('exact goal', result.stderr)


if __name__ == '__main__':
    unittest.main()
