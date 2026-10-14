"""Rolling neighbor hints against independent disjoint interval membership."""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest


class IntervalFinger(unittest.TestCase):
    def test_forward_backward_gaps_rotations_and_maximum_key(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        rng = random.Random(783216)
        rows = []
        for trial in range(160):
            count = rng.randrange(2, 200)
            entries = [dict(start=i * 7 + 1, end=i * 7 + 5, value=i + 1)
                       for i in range(count)]
            keys = list(range(count * 7 + 2))
            keys += list(reversed(keys))
            keys += [rng.randrange(count * 7 + 20) for _ in range(300)]
            rng.shuffle(entries)
            expected = [next((e['value'] for e in entries
                             if e['start'] <= key < e['end']), 0) for key in keys]
            rows.append(dict(entries=[{**e, 'start': str(e['start']),
                                       'end': str(e['end'])} for e in entries],
                             keys=list(map(str, keys)), expected=expected))
        rows.append(dict(entries=[dict(start='18446744073709551610', end='0', value=7)],
                         keys=['18446744073709551610', '18446744073709551615', '0',
                               '18446744073709551615'], expected=[7, 7, 0, 7]))
        with tempfile.TemporaryDirectory() as directory:
            d = Path(directory)
            result = subprocess.run(
                [compiler, 'build', root / os.environ.get('INK_INTERVAL_SOURCE', 'examples/crdts/interval_finger.ink'),
                 '--target', 'javascript', '-o', d / 'compiled.mjs'],
                capture_output=True, text=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr[-3000:])
            (d / 'cases.json').write_text(json.dumps(rows))
            (d / 'verify.mjs').write_text("""
import assert from 'node:assert/strict';import fs from 'node:fs';
import {functions} from './compiled.mjs';
for (const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))) {
 const entries=row.entries.map(e=>({...e,start:BigInt(e.start),end:BigInt(e.end)}));
 assert.deepEqual(functions.rolling(entries,row.keys.map(BigInt)),row.expected);
}
assert.deepEqual(functions.split_hint(),[2,2,2]);
console.log('PASS rolling hints through independent forward/backward/gap queries');
""")
            result = subprocess.run(['node', d / 'verify.mjs'],
                                    capture_output=True, text=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr[-3000:])


if __name__ == '__main__':
    unittest.main()
