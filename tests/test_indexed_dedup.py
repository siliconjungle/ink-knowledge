"""Replay composed representation proofs, reject forgeries, execute exact output."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from producers.indexed_dedup import write

class IndexedDedup(unittest.TestCase):
 def test_composed_proof_selection_execution_and_rehashed_false_result(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);source,proofs=write(d)
   def run(*args):
    r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=120)
    self.assertEqual(r.returncode,0,r.stderr[-3000:]);return r
   report=json.loads(run(compiler,'emit-laws',source,'--proofs',proofs,'-o',d/'bundle.json').stdout)
   self.assertEqual(report['status'],'checked');self.assertEqual(len(report['names']),32)
   bundle=json.loads((d/'bundle.json').read_text());law=report['names']['dedup_indexed']
   helper=(root/'knowledge/libraries/indexed-dedup-u32.ink').read_text().split('law index_membership')[0]
   program=helper+'\npub fn run(xs:List<u32>)->List<u32>{return foldl(xs,empty_words(),fn(item,acc)=>dedup_step(item,acc));}\n'
   (d/'program.ink').write_text(program)
   run(compiler,'emit-core',d/'program.ink','-o',d/'core.json');run(compiler,'emit-semantic',d/'core.json','--core','-o',d/'subject.json')
   subject=json.loads((d/'subject.json').read_text())
   selection=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=bundle,
    applications=[dict(function='run',path=[],law=law,arguments={'xs':dict(sort={'Value':{'List':'U32'}},node={'Free':'xs'})},premises=[])])
   (d/'selection.json').write_bytes(canonical(selection))
   run(compiler,'check-selection',d/'core.json',d/'selection.json')
   for name,extra in [('baseline',[]),('selected',['--selection',d/'selection.json'])]:
    run(compiler,'build',d/'core.json','--core','--target','javascript',*extra,'-o',d/(name+'.mjs'))
   (d/'verify.mjs').write_text('''import assert from 'node:assert/strict';import * as a from './baseline.mjs';import * as b from './selected.mjs';
for(const n of [0,1,2,9,127])for(const mode of [0,1,2]){
 const xs=Array.from({length:n},(_,i)=>[0xffffffff,0,17,Math.imul(i,2654435761)>>>0][mode===0?3:i%4]);
 if(mode===2)xs.reverse();const before=xs.slice(),expected=[...new Set(xs)];
 assert.deepEqual(a.call('run',[xs]),expected);assert.deepEqual(b.call('run',[xs]),expected);assert.deepEqual(xs,before);
}
''');run('node',d/'verify.mjs')
   # New content hashes and valid snapshot membership do not repair false proofs.
   objects=copy.deepcopy(bundle['objects']);bad=objects.pop(law);bad['payload']['to']={'sort':{'Value':{'List':'U32'}},'node':'Nil'}
   bad_id=identity(bad);objects[bad_id]=bad;bank=Store.publish(d/'forged',objects.values())
   forged=copy.deepcopy(selection);forged['applications'][0]['law']=bad_id;forged['knowledge']=bank.bundle([bad_id]);(d/'forged.json').write_bytes(canonical(forged))
   result=subprocess.run([str(compiler),'check-selection',str(d/'core.json'),str(d/'forged.json')],capture_output=True,text=True,timeout=120)
   self.assertNotEqual(result.returncode,0,'rehashed empty output must not be admitted')
   # Rebinding the source hash cannot transfer proofs to a changed helper meaning.
   (d/'changed.ink').write_text(program.replace('key==item||found','key!=item||found'))
   run(compiler,'emit-core',d/'changed.ink','-o',d/'changed-core.json');run(compiler,'emit-semantic',d/'changed-core.json','--core','-o',d/'changed-subject.json')
   changed=copy.deepcopy(selection);changed['input_core_sha256']=json.loads((d/'changed-subject.json').read_text())['input_core_sha256'];(d/'changed-selection.json').write_bytes(canonical(changed))
   result=subprocess.run([str(compiler),'check-selection',str(d/'changed-core.json'),str(d/'changed-selection.json')],capture_output=True,text=True,timeout=120)
   self.assertNotEqual(result.returncode,0,'a changed membership helper must invalidate its proof context')

if __name__=='__main__':unittest.main()
