"""Force common-prefix shredding and gap/span transitions against the list model."""
import json,os,random
from pathlib import Path
import subprocess,tempfile,unittest
from test_span_event_graph import Oracle,generated

def phased_cases(count=100,run=8):
 rng=random.Random(830155);rows=[]
 for history in range(count):
  model=Oracle();changes=[];counters={a:(100 if history%2 else 1) for a in range(1,5)}
  def add(parents,clear=False):
   view=model.visible(model.closure(parents));position=0 if clear else rng.randrange(len(view)+1)
   remove=len(view) if clear else rng.randrange(min(5,len(view)-position)+1)
   text=[] if clear and remove else [rng.choice([0,65,233,128578,1114111]) for _ in range(rng.randrange(1 if remove==0 else 0,5))]
   actor=rng.randrange(1,5);identity=(actor<<32)|counters[actor]
   counters[actor]+=remove+len(text)
   c=dict(id=identity,parents=parents,position=position,remove=remove,text=text)
   model.apply(c,len(changes)+1);changes.append(c)
   return identity+remove+len(text)-1
  last=add([]);older=last
  for cycle in range(4):
   for _ in range(run):last=add([last])
   left=add([last]);right=add([last])
   parents=[left,right]+([older] if cycle%2 else [])
   last=add(parents,clear=(cycle==2 and history%3==0))
  for _ in range(run):last=add([last])
  # The largest operation identity must remain disjoint from the baseline.
  c=dict(id=18446744073709551615,parents=[last],position=0,remove=0,text=[1114111])
  model.apply(c,len(changes)+1);changes.append(c)
  rows.append(dict(name=f'phased-{history}',changes=changes,expected=model.result()))
 return rows

class PhasedEventGraph(unittest.TestCase):
 def test_shredding_forks_overlapping_deletes_sparse_ids_and_redundant_parents(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  rows=phased_cases()+phased_cases(count=4,run=140)+generated(seed=830156,count=200,maximum=30)
  with tempfile.TemporaryDirectory() as td:
   d=Path(td);source=root/os.environ.get('INK_PHASED_SOURCE','examples/crdts/phased_graph.ink')
   build=subprocess.run([compiler,'build',source,'--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180)
   self.assertEqual(build.returncode,0,build.stderr[-2500:])
   # Wire u64 strings avoid loss of precision in JavaScript JSON numbers.
   for row in rows:
    for c in row['changes']:c['id']=str(c['id']);c['parents']=list(map(str,c['parents']))
   (d/'cases.json').write_text(json.dumps(rows))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';
import fs from 'node:fs';
import {functions} from './compiled.mjs';
const rows=JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)));
for(const row of rows){
 const changes=row.changes.map(c=>({...c,id:BigInt(c.id),parents:c.parents.map(BigInt)}));
 const want={Ok:row.expected};
 assert.deepEqual(functions.scalar(changes),want,row.name+' scalar/model');
 assert.deepEqual(functions.small_phases(changes),want,row.name+' phased/model');
 assert.deepEqual(functions.zero_phases(changes),want,row.name+' zero threshold/model');
 if(row.name.startsWith('phased-'))assert.ok(functions.enabled(changes,2)>0,row.name+' actually applicable');
 if(changes.length>500)assert.ok(functions.enabled(changes,128)>0,row.name+' production threshold');
 assert.deepEqual(functions.materialize(changes),want,row.name+' default/model');
}
const base={id:4294967297n,parents:[],position:0,remove:0,text:[65,66,67,68]};
for(const bad of [
 {id:8589934593n,parents:[4294967300n],position:8,remove:0,text:[65]},
 {id:8589934593n,parents:[4294967300n],position:0,remove:9,text:[]},
 {id:8589934593n,parents:[4294967300n],position:0,remove:0,text:[55296]},
 {id:4294967299n,parents:[4294967300n],position:0,remove:0,text:[65]},
 {id:8589934593n,parents:[99n],position:0,remove:0,text:[65]},
 {id:8589934593n,parents:[4294967298n],position:1,remove:0,text:[65]},
]){
 const history=[base,bad];
 assert.deepEqual(functions.small_phases(history),functions.scalar(history),'error/fallback');
 assert.deepEqual(functions.zero_phases(history),functions.scalar(history),'zero error/fallback');
}
console.log('PASS '+rows.length+' histories plus errors/fallbacks');
""")
   run=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180)
   self.assertEqual(run.returncode,0,run.stderr[-3000:])
if __name__=='__main__':unittest.main()
