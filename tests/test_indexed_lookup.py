"""Discover, replay and execute indexed batches without a compiler recogniser."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry,entry
from ink_knowledge.proposals import SEMANTICS
from producers.indexed_lookup import specialize

SOURCE='''module independent_lookup;
record Query { key:u32, unused:u64, }
fn membership(keys:List<u32>,queries:List<Query>,offset:u32)->List<Bool>{
 return queries.map(fn(q)=>foldr(keys,false,fn(item)=>fn(found)=>(q.key+offset)==item||found));
}
fn filtered(keys:List<u64>,queries:List<u64>)->List<u64>{
 return queries.filter(fn(key)=>foldr(keys,false,fn(item)=>fn(found)=>key==item||found));
}
fn dependent(queries:List<List<u32>>)->List<Bool>{
 return queries.map(fn(keys)=>foldr(keys,false,fn(item)=>fn(found)=>17==item||found));
}
fn floating(keys:List<f32>,queries:List<f32>)->List<Bool>{
 return queries.map(fn(key)=>foldr(keys,false,fn(item)=>fn(found)=>key==item||found));
}
'''

class IndexedLookup(unittest.TestCase):
 def test_checked_discovery_execution_and_forged_index(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);source=d/'source.ink';source.write_text(SOURCE)
   def run(*args,**kw):
    r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=120,**kw)
    self.assertEqual(r.returncode,0,r.stderr[-3000:]);return r
   core=d/'core.json';subject=d/'subject.json'
   run(compiler,'emit-core',source,'-o',core);run(compiler,'emit-semantic',source,'-o',subject)
   checked=json.loads(core.read_text());meaning=json.loads(subject.read_text());rows=specialize(meaning,checked)
   self.assertEqual(len(rows),4)
   self.assertFalse(any(n.startswith(('dependent_','floating_'))for n,_ in rows))
   objects={identity(semantic_entry(l)):semantic_entry(l)for _,l in rows}
   good=Store.publish(d/'proofs',objects.values())
   for name,law in rows:
    key=identity(semantic_entry(law));view=d/'view.json';view.write_bytes(canonical(good.bundle([key])))
    run(compiler,'knowledge-check',core,view)
    if name.startswith('index_membership_'):
     forged=copy.deepcopy(law);forged['to']['node']['Op'][1][1]={'sort':law['params']['indexed_key'],'node':{'Word':0}}
     bad=semantic_entry(forged);bank=Store.publish(d/'forged',[bad]);view.write_bytes(canonical(bank.bundle([identity(bad)])))
     r=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],capture_output=True,text=True,timeout=120)
     self.assertNotEqual(r.returncode,0,'a rehashed wrong lookup key was admitted')
   producer=entry('definition',SEMANTICS,dict(module='producers.indexed_lookup'))
   bank=Store.publish(d/'knowledge',[producer]);costs=d/'costs.json'
   costs.write_text(json.dumps(dict(schema=1,operation_costs={'estimate:loop_iterations':128,'estimate:let_binding':0,'call:foldr':10000,'call:fold_until':10000,'method:contains':1})))
   selection=d/'selection.json';environment=dict(os.environ,PYTHONPATH=os.pathsep.join(map(str,[root/'knowledge',root/'planner'])))
   report=json.loads(run('python3','-m','ink_planner.semantic_search','--compiler',compiler,'--core',core,'--snapshot',bank.data/'snapshot.json','--knowledge-root',bank.root,'--cost-model',costs,'--diagnostics',d/'near.json','--budget','32','--rounds','4','--time-seconds','30','-o',selection,env=environment).stdout)
   self.assertTrue(any(p['module']=='producers.indexed_lookup'and p['candidates']for p in report['database']['producers']))
   chosen={a['law']for a in json.loads(selection.read_text())['applications']}
   # Discovery may compose an equivalent filter law. Check admission of both
   # proposals, and selection of the indexed map under these synthetic prices.
   diagnostics=json.loads((d/'near.json').read_text())['laws']
   for name,law in rows:
    key=identity(semantic_entry(law))
    if not name.startswith('index_membership_'):
     self.assertGreater(diagnostics[key]['admitted'],0)
    if name.startswith('membership_indexed_lookup_'):
     self.assertIn(key,chosen)
   run(compiler,'check-selection',core,selection)
   # Execute the exact indexed map AND filter proposals independently of which
   # equivalent chain wins the planner's synthetic cost comparison.
   roots=[];applications=[]
   for name,law in rows:
    if name.startswith('index_membership_'):continue
    key=identity(semantic_entry(law));roots.append(key)
    applications.append(dict(function=name.split('_indexed_lookup_')[0],path=[],law=key,
     arguments={n:{'sort':s,'node':{'Free':n}}for n,s in law['params'].items()},premises=[]))
   selection=d/'indexed-selection.json'
   selection.write_bytes(canonical(dict(schema=1,semantics='ink-evidence-v1',
    input_core_sha256=meaning['input_core_sha256'],knowledge=good.bundle(roots),applications=applications)))
   run(compiler,'check-selection',core,selection)
   run(compiler,'build',core,'--core','--target','javascript','-o',d/'baseline.mjs')
   run(compiler,'build',core,'--core','--target','javascript','--selection',selection,'-o',d/'selected.mjs')
   script=d/'verify.mjs';script.write_text('''import assert from 'node:assert/strict';
import {functions as a} from './baseline.mjs';import {functions as b} from './selected.mjs';
for(const n of [0,1,2,7,31,127])for(const count of [0,1,3,17])for(const offset of [0,1,0xffffffff]){
 const keys=Array.from({length:n},(_,i)=>(Math.imul(i,0x98765431)+17)>>>0);if(n>1)keys[n-1]=keys[0];
 const qs=Array.from({length:count},(_,i)=>i%2===0?(keys[i%n]??0):i);
 const queries=qs.map(key=>({key,unused:0xffffffffffffffffn}));const expected=qs.map(k=>keys.includes((k+offset)>>>0));
 assert.deepEqual(a.membership(keys,queries,offset),expected);assert.deepEqual(b.membership(keys,queries,offset),expected);
 const wide=keys.map(k=>BigInt(k)+0xffffffff00000000n),wideq=qs.map(k=>BigInt(k)+0xffffffff00000000n);
 const filtered=wideq.filter(k=>wide.includes(k));assert.deepEqual(a.filtered(wide,wideq),filtered);assert.deepEqual(b.filtered(wide,wideq),filtered);
}
''');run('node',script)

if __name__=='__main__':unittest.main()
