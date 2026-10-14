"""Stable-slot block sequence against two treaps and independent positions."""
import json,os,random,subprocess,tempfile,unittest
from pathlib import Path

class BlockedMeasure(unittest.TestCase):
 def test_mixed_mutations_and_all_measure_queries(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(391805);rows=[]
  for trial in range(153):
   edits=[];order=[];items={};slot=1
   for step in range(180 if trial<150 else 2200):
    kind=0 if not order or (trial>=150 and step<1500) else rng.randrange(5);target=0 if not order else rng.choice(order+[0]);extent=rng.randrange(7);a=rng.randrange(7);b=rng.randrange(7)
    edits.append(dict(kind=kind,slot=target,value=slot,extent=extent,first=a,second=b))
    if kind==0:
     order.insert(order.index(target)if target else len(order),slot);items[slot]=[extent,a,b];slot+=1
    elif target:
     if kind==1:items[target][1]=a
     elif kind==2:items[target][2]=b
     elif kind==3:items[target]=[extent,a,b]
     else:items[target][1:]=[a,b]
   expected=[]
   for measure in range(3):
    values=[]
    for position in range(sum(items[i][measure]for i in order)+2):
     left=position;node=offset=0
     for i in order:
      if left<items[i][measure]:node=i;offset=left;break
      left-=items[i][measure]
     values.extend([node,offset])
    expected.append(values)
   ranks=[[0]+[sum(items[j][measure]for j in order[:order.index(i)])for i in range(1,slot)]for measure in range(3)]
   rows.append(dict(edits=edits,expected=expected,ranks=ranks,order=order,totals=[sum(items[i][m] for i in order) for m in range(3)]))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);source=root/os.environ.get('INK_BLOCKED_SOURCE','examples/crdts/blocked_measure.ink');r=subprocess.run([compiler,'build',source,'--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:]);(d/'cases.json').write_text(json.dumps(rows))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';import fs from 'node:fs';import {functions} from './compiled.mjs';
const rows=JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)));
for(const row of rows){const totals=functions.totals(row.edits);for(let m=0;m<3;m++){assert.equal(totals[m*2],totals[m*2+1]);assert.equal(totals[m*2],row.totals[m]);}
assert.deepEqual(functions.linked(row.edits),row.order);
for(let measure=0;measure<3;measure++){const want=row.expected[measure],queries=Array.from({length:want.length/2},(_,i)=>i),actual=functions.positions(row.edits,queries,measure);
for(let i=0;i<actual.length;i+=6){assert.equal(actual[i],actual[i+1]);assert.equal(actual[i+2],actual[i+3]);assert.equal(actual[i+4],actual[i+5]);assert.equal(actual[i],want[i/3]);if(actual[i])assert.equal(actual[i+4],want[i/3+1]);}
const wantedRanks=row.ranks[measure],gotRanks=functions.ranks(row.edits,Array.from({length:wantedRanks.length},(_,i)=>i),measure);for(let i=0;i<gotRanks.length;i+=2){assert.equal(gotRanks[i],gotRanks[i+1]);assert.equal(gotRanks[i],wantedRanks[i/2]);}
}}
const edits=Array.from({length:3500},(_,i)=>({kind:0,slot:0,value:i+1,extent:1,first:1,second:1}));
const stats=functions.totals(edits);assert.ok(stats[6]>64);for(let i=0;i<6;i++)assert.equal(stats[i],3500);
assert.deepEqual(functions.linked(edits),Array.from({length:3500},(_,i)=>i+1));
const positions=[0,15,16,31,32,511,512,1023,3499,3500,4294967295];
for(let m=0;m<3;m++){const got=functions.positions(edits,positions,m);for(let i=0;i<got.length;i+=6){if(positions[i/6]!==4294967295)assert.equal(got[i],got[i+1]);assert.equal(got[i],positions[i/6]<3500?positions[i/6]+1:0);if(got[i])assert.equal(got[i+4],got[i+5]);}
const ranks=functions.ranks(edits,[0,1,16,17,32,33,512,513,3500],m);for(let i=0;i<ranks.length;i+=2)assert.equal(ranks[i],ranks[i+1]);}
console.log('PASS '+rows.length+' mixed histories and a 3500-item multilevel split case');""")
   r=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:]);print(r.stdout.strip())
if __name__=='__main__':unittest.main()
