"""Independent sequence measures preserve both maintained-tree projections."""
import json,os,random,subprocess,tempfile,unittest
from pathlib import Path

class DualMeasure(unittest.TestCase):
 def test_mixed_mutations_and_all_measure_queries(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(391805);rows=[]
  for _ in range(150):
   edits=[];order=[];items={};slot=1
   for step in range(70):
    kind=0 if not order else rng.randrange(5);target=0 if not order else rng.choice(order+[0]);extent=rng.randrange(7);a=rng.randrange(7);b=rng.randrange(7)
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
   rows.append(dict(edits=edits,expected=expected,ranks=ranks))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);r=subprocess.run([compiler,'build',root/'examples/crdts/dual_measure.ink','--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:]);(d/'cases.json').write_text(json.dumps(rows))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';import fs from 'node:fs';import {functions} from './compiled.mjs';
const rows=JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)));
for(const row of rows){const image=functions.images(row.edits);assert.equal(image.length%29,0);for(let i=0;i<image.length;i+=29){
 for(const [a,b] of [[0,1],[0,2],[3,4],[3,5],[6,7],[8,9],[10,11],[12,13],[14,15],[14,16],[17,18],[17,19],[20,21],[20,22],[23,24],[23,25],[26,27],[26,28]])assert.equal(image[i+a],image[i+b]);
}for(let measure=0;measure<3;measure++){const want=row.expected[measure],queries=Array.from({length:want.length/2},(_,i)=>i),actual=functions.positions(row.edits,queries,measure);
for(let i=0;i<actual.length;i+=6){assert.equal(actual[i],actual[i+1]);assert.equal(actual[i+2],actual[i+3]);assert.equal(actual[i+4],actual[i+5]);assert.equal(actual[i],want[i/3]);if(actual[i])assert.equal(actual[i+4],want[i/3+1]);}
const wantedRanks=row.ranks[measure],gotRanks=functions.ranks(row.edits,Array.from({length:wantedRanks.length},(_,i)=>i),measure);for(let i=0;i<gotRanks.length;i+=2){assert.equal(gotRanks[i],gotRanks[i+1]);assert.equal(gotRanks[i],wantedRanks[i/2]);}
}}
console.log('PASS '+rows.length+' histories, both projected trees and independent positions');""")
   r=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:]);print(r.stdout.strip())
if __name__=='__main__':unittest.main()
