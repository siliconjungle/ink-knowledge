"""Exact maintained metadata after insertion and multilevel block splitting."""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest


class SuffixMeasure(unittest.TestCase):
    def test_entire_constructor_maintained_tree_matches_full_reindexing(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        rng = random.Random(281209)
        rows = []
        for trial in range(90):
            edits, order, slot = [], [], 1
            for index in range(96):
                kind = 0 if not order or trial < 3 else rng.randrange(5)
                target = rng.choice(order + [0]) if order else 0
                if trial == 0:
                    target = 0
                elif trial == 1:
                    target = order[0] if order else 0
                edits.append(dict(kind=kind, slot=target, value=slot,
                                  extent=rng.randrange(7), first=rng.randrange(7),
                                  second=rng.randrange(7)))
                if kind == 0:
                    order.insert(order.index(target) if target else len(order), slot)
                    slot += 1
                if index < 40 or index in (63, 64, 95):
                    rows.append(edits.copy())
        # Grow through leaf and branch splits at both ends and interior slots.
        for mode in range(3):
            edits = [dict(kind=0, slot=0 if mode == 0 or i == 0 else
                          (1 if mode == 1 else 1 + i // 2), value=i + 1,
                          extent=i % 5, first=i % 3, second=i % 7)
                     for i in range(3500)]
            rows.append(edits)
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            result = subprocess.run(
                [compiler, 'build', root / 'examples/crdts/suffix_measure.ink',
                 '--target', 'javascript', '-o', d / 'compiled.mjs'],
                capture_output=True, text=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr[-3000:])
            (d / 'cases.json').write_text(json.dumps(rows))
            (d / 'verify.mjs').write_text("""
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {functions} from './compiled.mjs';
const rows=JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)));
for (const [index, edits] of rows.entries()) {
  assert.deepEqual(functions.metadata(edits), functions.original_metadata(edits),
                   `complete maintained tree ${index}`);
}
console.log(`PASS ${rows.length} exact maintained metadata comparisons`);
""")
            result = subprocess.run(['node', d / 'verify.mjs'],
                                    capture_output=True, text=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr[-3000:])
            print(result.stdout.strip())


if __name__ == '__main__':
    unittest.main()
