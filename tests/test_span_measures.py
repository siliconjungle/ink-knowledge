"""Check maintained measures after every causal batch, independently of text output."""
import json,os
from pathlib import Path
import subprocess,tempfile,unittest
from test_span_event_graph import generated

class SpanMeasures(unittest.TestCase):
 def test_exact_measurement_invariant_after_every_batch(self):
  root=Path(__file__).resolve().parents[2]
  compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  rows=generated(count=400)
  for row in rows:
   for change in row['changes']:
    change['id']=str(change['id']);change['parents']=list(map(str,change['parents']))
  with tempfile.TemporaryDirectory() as td:
   d=Path(td)
   build=subprocess.run([compiler,'build',root/'examples/crdts/span_measures.ink','--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180)
   self.assertEqual(build.returncode,0,build.stderr[-2000:])
   (d/'cases.json').write_text(json.dumps(rows))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';
import fs from 'node:fs';
import {functions} from './compiled.mjs';
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){
 const changes=row.changes.map(c=>({...c,id:BigInt(c.id),parents:c.parents.map(BigInt)}));
 assert.equal(functions.valid_measures(changes),true,row.name);
}
""")
   run=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180)
   self.assertEqual(run.returncode,0,run.stderr[-2000:])
if __name__=='__main__':unittest.main()
