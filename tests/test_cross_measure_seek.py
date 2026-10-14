"""All cross-measure queries against independent flat ordered items."""
import json,os,random,subprocess,tempfile,unittest
from pathlib import Path
class CrossMeasureSeek(unittest.TestCase):
 def test_mixed_weights_zero_extents_and_multilevel_splits(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(729152);rows=[]
  histories=[]
  for trial in range(123):
   edits=[];order=[];items={};slot=1
   for step in range(180 if trial<120 else 2200):
    kind=0 if not order or (trial>=120 and step<1500)else rng.randrange(5);target=rng.choice(order+[0])if order else 0;measures=[rng.randrange(7)for _ in range(3)]
    edits.append(dict(kind=kind,slot=target,value=slot,extent=measures[0],first=measures[1],second=measures[2]))
    if kind==0:order.insert(order.index(target)if target else len(order),slot);items[slot]=measures;slot+=1
    elif target:
     if kind==1:items[target][1]=measures[1]
     elif kind==2:items[target][2]=measures[2]
     elif kind==3:items[target]=measures
     else:items[target][1:]=measures[1:]
   histories.append((edits,order,items))
  histories.append(([dict(kind=0,slot=0,value=i+1,extent=1,first=i%3,second=i%7)for i in range(3500)],list(range(1,3501)),{i+1:[1,i%3,i%7]for i in range(3500)}))
  for edits,order,items in histories:
   for selection in range(3):
    total=sum(items[i][selection]for i in order)
    queries=list(range(total+2))if len(order)<100 else sorted(set([0,total,total+1,*[rng.randrange(total+1)for _ in range(100)],4294967295]))
    for observation in range(3):
     expected=[]
     for position in queries:
      remaining=position;rank=0;node=offset=0
      for i in order:
       if remaining<items[i][selection]:node=i;offset=remaining;break
       remaining-=items[i][selection];rank+=items[i][observation]
      expected.extend([node,rank if node else 0,offset])
     rows.append(dict(edits=edits,queries=queries,selection=selection,observation=observation,expected=expected))
  # Maximum selected extent and maximum observed prefix are both legitimate.
  for measures,selection,observation in [([[4294967295,1,0],[0,2,0]],0,1),([[0,4294967295,0],[4294967295,0,0]],0,1)]:
   edits=[dict(kind=0,slot=0,value=i+1,extent=a,first=b,second=c)for i,(a,b,c)in enumerate(measures)]
   queries=[0,1,4294967294,4294967295];node=1 if measures[0][0]else 2;rank=0 if node==1 else 4294967295
   rows.append(dict(edits=edits,queries=queries,selection=selection,observation=observation,expected=[node,rank,0,node,rank,1,node,rank,4294967294,0,0,0]))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);source=root/os.environ.get('INK_CROSS_SOURCE','examples/crdts/cross_measure_seek.ink');r=subprocess.run([compiler,'build',source,'--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:]);(d/'cases.json').write_text(json.dumps(rows))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';import fs from 'node:fs';import{functions}from'./compiled.mjs';
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url))))assert.deepEqual(functions.positions(row.edits,row.queries,row.selection,row.observation),row.expected);
console.log('PASS all independent cross-measure cases');""")
   r=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:])
if __name__=='__main__':unittest.main()
