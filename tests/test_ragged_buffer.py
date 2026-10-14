"""Flat variable-length rows preserve exact decoding and stable row boundaries."""
import json,os,random,subprocess,tempfile,unittest
from pathlib import Path
class RaggedBuffer(unittest.TestCase):
 def test_empty_rows_random_lengths_and_missing_row_queries(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(571002)
  cases=[[],[[]],[[],[1,2],[],[0,4294967295],[]]]
  cases.extend([[[rng.randrange(4294967296)for _ in range(rng.randrange(20))]for _ in range(rng.randrange(50))]for _ in range(100)])
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);source=root/os.environ.get('INK_RAGGED_SOURCE','examples/crdts/ragged_buffer.ink');r=subprocess.run([compiler,'build',source,'--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:]);(d/'cases.json').write_text(json.dumps(cases))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';import fs from 'node:fs';import{functions}from'./compiled.mjs';
for(const rows of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){const queries=[...rows.keys(),rows.length,rows.length+1,0xffffffff];assert.deepEqual(functions.selected(rows,queries),queries.map(i=>rows[i]??[]));
let offset=0;const ranges=rows.flatMap(row=>{const start=offset;offset+=row.length;return[start,offset];});assert.deepEqual(functions.layout(rows),ranges);}
console.log('PASS exact ragged rows and stable ranges');""")
   r=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:])
if __name__=='__main__':unittest.main()
