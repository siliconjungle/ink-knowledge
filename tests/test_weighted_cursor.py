"""Nearby cursor searches preserve the ordinary weighted sequence API."""
import json,os,random
from pathlib import Path
import subprocess,tempfile,unittest

def edit(kind,**kwargs):
 result=dict(kind=kind,slot=0,before=0,value=0,extent=0,weight=0,position=0,visible=True)
 result.update(kwargs);return result

def cases():
 rng=random.Random(891110);histories=[]
 for _ in range(400):
  order=[];weights={};extents={};events=[]
  for _ in range(140):
   kind=rng.randrange(5) if order else 0
   if kind==0:
    where=rng.randrange(len(order)+1);before=order[where] if where<len(order) else 0
    slot=len(order)+1;weight=rng.randrange(12);extent=rng.randrange(12)
    order.insert(where,slot);weights[slot]=weight;extents[slot]=extent
    events.append(edit(0,before=before,value=rng.randrange(1000),weight=weight,extent=extent))
    start=sum(weights[s] for s in order[:where])
    if weight:events.append(edit(3,position=start+rng.randrange(weight)))
   elif kind in [1,2]:
    slot=rng.choice(order);weights[slot]=rng.randrange(12)
    if kind==2:extents[slot]=rng.randrange(12)
    events.append(edit(kind,slot=slot,weight=weights[slot],extent=extents[slot]))
   elif kind==3:
    visible=rng.choice([True,False]);total=sum((weights if visible else extents).values())
    events.append(edit(3,position=rng.choice([0,total,total+1,4294967295,rng.randrange(total+1)]),visible=visible))
   else:events.append(edit(4,slot=rng.choice(order),visible=rng.choice([True,False])))
  histories.append(events)
 # Overflow permanently disables the cursor path; sentinel MAX retains the
 # original traversal's exact result without being cached as valid membership.
 histories.append([edit(0,weight=4294967293,extent=1),edit(3,position=5),edit(0,weight=10,extent=1),edit(3,position=5),edit(1,slot=1,weight=1),edit(3,position=2)])
 histories.append([edit(0,weight=3,extent=3),edit(3,position=4294967295),edit(3,position=1),edit(0,before=1,weight=2,extent=2),edit(3,position=0)])
 return histories

class WeightedCursor(unittest.TestCase):
 def test_rotations_adjacent_mutations_zero_weights_invalidation_and_overflow(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  with tempfile.TemporaryDirectory() as td:
   d=Path(td)
   build=subprocess.run([compiler,'build',root/'examples/crdts/weighted_cursor.ink','--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180)
   self.assertEqual(build.returncode,0,build.stderr[-2000:])
   rows=cases();(d/'cases.json').write_text(json.dumps(rows))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';
import fs from 'node:fs';
import {functions} from './compiled.mjs';
const rows=JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)));
for(let i=0;i<rows.length;i++)assert.equal(functions.same(rows[i]),true,'history '+i);
console.log('PASS '+rows.length+' cursor/ordinary histories');
""")
   run=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180)
   self.assertEqual(run.returncode,0,run.stderr[-2000:])
if __name__=='__main__':unittest.main()
