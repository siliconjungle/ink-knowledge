"""Exact interval refinement images and independent half-open membership."""
import json,os,random,subprocess,tempfile,unittest
from pathlib import Path
class IntervalPartition(unittest.TestCase):
 def test_parent_links_rotations_and_stale_hint_fallback(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(762191);rows=[]
  for trial in range(180):
   entries=[dict(start=i*100,end=i*100+90,value=i+1)for i in range(rng.randrange(1,20))];rng.shuffle(entries)
   intervals=[{**e,'hint':i+1}for i,e in enumerate(entries)];cuts=[]
   for k in range(35):
    choices=[e for e in intervals if e['end']-e['start']>1]
    if not choices:break
    e=rng.choice(choices);boundary=rng.randrange(e['start']+1,e['end']);suffix=len(entries)+len(cuts)+1;hint=e['hint']if k%3 else rng.randrange(len(intervals)+4)
    cuts.append(dict(start=e['start'],end=e['end'],boundary=boundary,value=e['value'],suffix=suffix,hint=hint))
    intervals.append(dict(start=boundary,end=e['end'],value=suffix,hint=suffix));e['end']=boundary
   keys=list(range(0,max(e['end']for e in entries)+2,13));expected=[next((e['value']for e in intervals if e['start']<=key<e['end']),0)for key in keys]
   rows.append(dict(entries=entries,cuts=cuts,keys=keys,expected=expected))
  maximum=(1<<64)-1
  rows.append(dict(entries=[dict(start=maximum-10,end=0,value=1)],cuts=[dict(start=maximum-10,end=0,boundary=maximum,value=1,suffix=2,hint=1)],keys=[maximum-10,maximum-1,maximum],expected=[1,1,2]))
  for cut in [dict(start=10,end=30,boundary=10,value=1,suffix=2,hint=1),dict(start=10,end=30,boundary=30,value=1,suffix=2,hint=1),dict(start=10,end=30,boundary=20,value=0,suffix=2,hint=1),dict(start=10,end=30,boundary=20,value=1,suffix=0,hint=1),dict(start=11,end=30,boundary=20,value=1,suffix=2,hint=1),dict(start=10,end=40,boundary=20,value=1,suffix=2,hint=1)]:
   rows.append(dict(entries=[dict(start=10,end=30,value=1)],cuts=[cut],keys=[0,10,19,20,29,30,39],expected=None))
  for row in rows:
   for e in row['entries']:
    for name in ['start','end']:e[name]=str(e[name])
   for c in row['cuts']:
    for name in ['start','end','boundary']:c[name]=str(c[name])
   row['keys']=list(map(str,row['keys']))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);r=subprocess.run([compiler,'build',root/'examples/crdts/interval_partition.ink','--target','javascript','-o',d/'compiled.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:]);(d/'cases.json').write_text(json.dumps(rows))
   (d/'verify.mjs').write_text("""import assert from 'node:assert/strict';import fs from 'node:fs';import{functions}from'./compiled.mjs';
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){
 const entries=row.entries.map(e=>({...e,start:BigInt(e.start),end:BigInt(e.end)}));
 const cuts=row.cuts.map(c=>({...c,start:BigInt(c.start),end:BigInt(c.end),boundary:BigInt(c.boundary)}));
 for(let i=0;i<=cuts.length;i++)assert.deepEqual(functions.image(entries,cuts.slice(0,i),true),functions.image(entries,cuts.slice(0,i),false));
 const keys=row.keys.map(BigInt),actual=functions.values(entries,cuts,keys,true);assert.deepEqual(actual,functions.values(entries,cuts,keys,false));if(row.expected!==null)assert.deepEqual(actual,row.expected);
}console.log('PASS exact refinement prefixes and independent membership');""")
   r=subprocess.run(['node',d/'verify.mjs'],capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode,0,r.stderr[-3000:])
if __name__=='__main__':unittest.main()
