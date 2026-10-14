"""One-pass interval insertion preserves exact maintained-tree state."""
import json,os,random,subprocess,tempfile,unittest
from pathlib import Path

class IntervalFused(unittest.TestCase):
 def test_rotations_boundaries_and_rejected_insertions(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(391784)
  rows=[]
  for _ in range(180):
   points=sorted(rng.sample(range(0,10000),rng.randrange(2,100)));entries=[dict(start=points[i],end=points[i+1],value=i+1)for i in range(0,len(points)-1,2)];rng.shuffle(entries)
   keys=points+[rng.randrange(10000)for _ in range(100)]
   expected=[next((e['value']for e in entries if e['start']<=k<e['end']),0)for k in keys]
   rows.append(dict(entries=entries,keys=keys,expected=expected))
   # Reject overlap on either side, duplicate keys, empty ranges and zero values.
   e=rng.choice(entries)
   for bad in [dict(start=e['start'],end=e['end'],value=99),dict(start=e['start']+1,end=e['end']+1,value=99),dict(start=e['start'],end=e['start'],value=99),dict(start=10001,end=10002,value=0)]:
    rows.append(dict(entries=entries+[bad],keys=[],expected=[]))
  maximum=(1<<64)-1
  for entries in [[],[dict(start=0,end=1,value=1)],[dict(start=maximum,end=0,value=7)],
    [dict(start=0,end=0,value=1),dict(start=maximum,end=0,value=7)],
    [dict(start=maximum-1,end=maximum,value=1),dict(start=maximum,end=0,value=2)]]:
   rows.append(dict(entries=entries,keys=[0,maximum-1,maximum],expected=None))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);source=root/'examples/crdts/interval_fused.ink'
   run=subprocess.run([compiler,'build',source,'--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(run.returncode,0,run.stderr[-3000:])
   for row in rows:
    for e in row['entries']:e['start']=str(e['start']);e['end']=str(e['end'])
    row['keys']=list(map(str,row['keys']))
   (d/'cases.json').write_text(json.dumps(rows))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';import fs from 'node:fs';import {functions} from './compiled.mjs';
const rows=JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)));
for(const row of rows){const entries=row.entries.map(e=>({...e,start:BigInt(e.start),end:BigInt(e.end)})),keys=row.keys.map(BigInt);
 for(let i=0;i<=entries.length;i++)assert.deepEqual(functions.image(entries.slice(0,i),true),functions.image(entries.slice(0,i),false),'exact prefix tree');
 const actual=functions.values(entries,keys,true);assert.deepEqual(actual,functions.values(entries,keys,false));
 if(row.expected!==null)assert.deepEqual(actual,row.expected);
}console.log('PASS '+rows.length+' interval histories');""")
   run=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(run.returncode,0,run.stderr[-3000:]);print(run.stdout.strip())
if __name__=='__main__':unittest.main()
