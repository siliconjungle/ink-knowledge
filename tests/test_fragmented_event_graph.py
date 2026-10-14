"""Interior-frontier splitting preserves the exact per-operation source trace."""
import json,os,random,subprocess,tempfile,unittest
from pathlib import Path
from test_span_event_graph import Oracle

def interior_histories(seed=391922,count=120):
 rng=random.Random(seed);rows=[]
 for _ in range(count):
  model=Oracle();changes=[];counters={};event_index=0
  for batch in range(rng.randrange(4,24)):
   ends=list(model.ancestors);parents=rng.sample(ends,rng.randrange(min(len(ends),3)+1));view=model.visible(model.closure(parents));position=rng.randrange(len(view)+1);remove=rng.randrange(min(5,len(view)-position)+1)
   text=[rng.choice([0,65,233,128578,1114111])for _ in range(rng.randrange(1 if remove==0 else 0,8))];actor=rng.randrange(1,5);start=counters.get(actor,1);identity=(actor<<32)|start;counters[actor]=start+remove+len(text)
   change=dict(id=identity,parents=parents,position=position,remove=remove,text=text);changes.append(change)
   for offset in range(remove+len(text)):
    event_index+=1;deleting=offset<remove;part=dict(id=identity+offset,parents=parents if offset==0 else[identity+offset-1],position=position if deleting else position+offset-remove,remove=1 if deleting else 0,text=[]if deleting else[text[offset-remove]])
    model.apply(part,event_index)
  rows.append(dict(changes=changes,expected=model.result()))
 return rows

class FragmentedEventGraph(unittest.TestCase):
 def test_exact_expansion_delete_insert_boundaries_and_scalar_values(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(391920);rows=[]
  for i in range(100):
   # A long initial insert, mixed replacement, and branches from arbitrary
   # scalar frontiers inside both deletion and insertion parts of replacement.
   width=rng.randrange(2,15);base=(1<<32)+1;second=(2<<32)+1;third=(3<<32)+1
   text=[rng.choice([0,65,233,128578,1114111])for _ in range(width)]
   removed=rng.randrange(1,width+1);inserted=rng.randrange(1,10);inside=rng.randrange(removed+inserted)
   replacement=dict(id=second,parents=[base+width-1],position=0,remove=removed,text=[66]*inserted)
   # Prefix view length after this particular scalar event.
   length=width-min(removed,inside+1)+max(0,inside+1-removed)
   changes=[dict(id=base,parents=[],position=0,remove=0,text=text),replacement,dict(id=third,parents=[second+inside],position=rng.randrange(length+1),remove=0,text=[67])]
   rows.append(changes)
  base=(1<<32)+1
  rows.extend([[dict(id=base,parents=[],position=0,remove=0,text=[65,66,67,68]),dict(id=(2<<32)+1,parents=[base+1,base+1],position=2,remove=0,text=[90])],
   [dict(id=(1<<64)-2,parents=[],position=0,remove=0,text=[65,66]),dict(id=base,parents=[(1<<64)-2],position=1,remove=0,text=[67])]])
  transported=[dict(changes=changes)for changes in rows]+interior_histories()
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);r=subprocess.run([compiler,'build',root/'examples/crdts/fragmented_graph.ink','--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:])
   for row in transported:
    for c in row['changes']:c['id']=str(c['id']);c['parents']=list(map(str,c['parents']))
   (d/'cases.json').write_text(json.dumps(transported));(d/'verify.mjs').write_text("""import assert from 'node:assert/strict';import fs from 'node:fs';import {functions as f} from './compiled.mjs';
const rows=JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)));
for(const row of rows){const c=row.changes.map(x=>({...x,id:BigInt(x.id),parents:x.parents.map(BigInt)}));assert.equal(f.valid(c),true);assert.deepEqual(f.fragment_events(c),f.original_events(c));const result=f.materialize(c);assert.deepEqual(result,f.scalar(c));if(row.expected)assert.deepEqual(result,{Ok:row.expected});}
const base={id:4294967297n,parents:[],position:0,remove:0,text:[65,66,67]};
for(const parent of [0n,99n,4294967300n]){const c=[base,{id:8589934593n,parents:[parent],position:0,remove:0,text:[66]}];assert.equal(f.valid(c),false);assert.deepEqual(f.materialize(c),f.scalar(c));}
console.log('PASS '+rows.length+' exact event histories plus invalid parents');""")
   r=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:]);print(r.stdout.strip())
if __name__=='__main__':unittest.main()
