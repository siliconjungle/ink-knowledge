"""Bounded sums retain overflow semantics under maintained word summaries."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import canonical
from producers.generic_indexed import generate
from test_generic_indexed import rehash,ROOT,COMPILER

class ModularAggregates(unittest.TestCase):
 def test_sum_fusion_and_authenticated_false_scalar_certificate(self):
  with tempfile.TemporaryDirectory(prefix='ink-modular-test-')as temporary:
   root=Path(temporary);source=root/'source.ink';model=root/'model.json'
   source.write_text('module modular;state Rows:Table<u64,u32> = Table.empty();change put(k:u64,v:u32)->Unit writes(Rows){Rows.put(k,v);return ();}query total()->u32 reads(Rows){return sum(Rows.values());}')
   subprocess.run([str(COMPILER),'emit-action-model',str(source),'-o',str(model)],check=True,capture_output=True)
   os.environ['INK_COMPILER']=str(COMPILER)
   result=generate(json.loads(model.read_text()),root/'database');request=result['request']
   self.assertTrue(any(row['action']=='total'for row in result['discovery']))
   path=root/'request.json';path.write_bytes(canonical(request)+b'\n')
   checked=subprocess.run([str(COMPILER),'check-representation',str(source),str(path)],capture_output=True,text=True,timeout=600)
   self.assertEqual(checked.returncode,0,checked.stderr)
   for mode,output in [('build',root/'literal.mjs'),('emit-representation',root/'indexed.mjs')]:
    command=[str(COMPILER),mode,str(source)]
    if mode=='emit-representation':command.append(str(path))
    subprocess.run([*command,'--target','javascript','-o',str(output)],check=True,capture_output=True,timeout=600)
   (root/'check.mjs').write_text("""import assert from 'node:assert/strict';import{createState as literal}from'./literal.mjs';import{createState as indexed}from'./indexed.mjs';
const states=[literal(),indexed()];
for(const [key,value]of [[1n,4294967295],[2n,4294967295],[3n,3],[1n,0]]){
 const replies=[];for(const state of states){replies.push(await state.invoke_json('put',[key,value]));}
 assert.deepEqual(replies[0],replies[1]);const sums=[];for(const state of states)sums.push((await state.invoke_json('total',[])).result);
 assert.deepEqual(sums[0],sums[1]);
}
assert.equal((await states[1].invoke_json('total',[])).result,2);
assert.deepEqual(await states[0].checkpoint(),await states[1].checkpoint());
""")
   operational=subprocess.run(['node',str(root/'check.mjs')],capture_output=True,text=True,timeout=120)
   self.assertEqual(operational.returncode,0,operational.stderr)
   objects=request['knowledge']['objects']
   selected=next(i for i,o in objects.items()if o['payload'].get('declaration',{}).get('Theorem',{}).get('params')==[['modular_head','U64'],['modular_tail','U64']])
   bad=copy.deepcopy(objects[selected]);theorem=bad['payload']['declaration']['Theorem'];theorem['to']={'U64':0};theorem['proof']['BitVector']['to']={'U64':0}
   forged=rehash(request,selected,bad,root/'forged');path.write_bytes(canonical(forged)+b'\n')
   rejected=subprocess.run([str(COMPILER),'check-representation',str(source),str(path)],capture_output=True,text=True,timeout=600)
   self.assertNotEqual(rejected.returncode,0)
   self.assertRegex(rejected.stderr,r'bitvector|bit proof|certificate|equality')

if __name__=='__main__':unittest.main()
