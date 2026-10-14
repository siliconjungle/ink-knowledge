"""Stable split links and replay against independently maintained partitions."""
import json,os,random,subprocess,tempfile,unittest
from pathlib import Path
class RefinementChain(unittest.TestCase):
 def test_original_handle_and_refinement_chain_survive_arbitrary_split_order(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(864321);cases=[]
  histories=[[],list(range(65)),list(reversed(range(65))),[32,16,48,8,24,40,56]*20]
  histories += [[rng.choice([*range(66),4294967295])for _ in range(rng.randrange(1,180))]for _ in range(240)]
  for cuts in histories:
   parts=[dict(start=0,length=0,next=0,payload=0),dict(start=1,length=64,next=0,payload=0)]
   for cut in cuts:
    key=1+cut
    for slot,p in enumerate(parts[1:],1):
     if p['start']<key<p['start']+p['length']:
      offset=key-p['start'];fresh=len(parts);suffix=dict(start=key,length=p['length']-offset,next=p['next'],payload=p['payload']+offset)
      p.update(length=offset,next=fresh);parts.append(suffix);break
   links=[n for p in parts for n in [p['start'],p['length'],p['next'],p['payload']]]
   replay=[n for slot,p in enumerate(parts)for n in [int(slot!=0),0,p['next']]]
   cases.append(dict(cuts=cuts,links=links,replay=replay))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);result=subprocess.run([compiler,'build',root/'examples/crdts/refinement_chain.ink','--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(result.returncode,0,result.stderr[-3000:]);(d/'cases.json').write_text(json.dumps(cases))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';import fs from 'node:fs';import{functions}from'./compiled.mjs';
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){assert.deepEqual(functions.links(row.cuts),row.links);assert.deepEqual(functions.replay(row.cuts),row.replay);}
console.log('PASS independent refinement links and off/on replay');""")
   result=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(result.returncode,0,result.stderr[-3000:])
if __name__=='__main__':unittest.main()
