import json,subprocess,tempfile,unittest
from pathlib import Path
from producers.boundary_readers import candidates
from producers.physical_capabilities import invoke,write
from producers.workspace import compiler_path
from ink_knowledge.recipes import load
from ink_knowledge.selection_probes import create

class BoundaryReaders(unittest.TestCase):
 def test_registry_and_general_usage_profiles_cover_wire_modes(self):
  registry,_=load();recipe=next(r for r in registry['recipes']if r['id']=='boundary-readers')
  self.assertEqual(recipe['parameters']['formats'],['compact','portable'])
  core=dict(program=dict(records={},functions=[dict(name='copy',params=[['rows',{'List':'U32'}]],result={'List':'U32'})]))
  spec,receipt=create(core,target='javascript')
  self.assertEqual(spec['schema'],3);self.assertEqual(set(receipt['boundaries']),{'trusted','portable','compact'})
  self.assertEqual({row['boundary']for rows in spec['phases'].values()for row in rows},{'trusted','portable','compact'})
  self.assertLessEqual(receipt['calls'],384)
  # Selection evidence now separates sizes rather than combining them in a
  # single boundary phase. Keep complete coverage and homogeneous strata.
  for mode in ['trusted','portable','compact']:
   phases=[rows for phase,rows in spec['phases'].items()if receipt['size_strata'][phase]['original_phase']=='call:copy:'+mode]
   self.assertEqual({len(row['args'][0])for rows in phases for row in rows},{0,8,128,2048})
   self.assertTrue(all(len({len(row['args'][0])for row in rows})==1 for rows in phases))
 def test_registry_proposals_compose_without_domain_recognisers(self):
  compiler=compiler_path()
  with tempfile.TemporaryDirectory()as temporary:
   root=Path(temporary);source=root/'source.ink'
   source.write_text('module packets; fn echo(rows:List<u32>)->List<u32>{return rows;} fn owned(rows:List<u32>)->Buffer<u32>{return buffer(rows);}')
   core=root/'core.json';invoke(compiler,'emit-core',source,'-o',core)
   context=dict(compiler=str(compiler),core=json.loads(core.read_bytes()),emit_target='javascript')
   proposals=list(candidates(context));self.assertEqual(len(proposals),6)
   for proposal in proposals:self.assertTrue(all(row['function']=='echo'for row in proposal['step']['package']['boundary_readers']))
   chosen=proposals[2]['step']['package']
   self.assertEqual(list(candidates(dict(context,physical=chosen))),[])
   plan=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=chosen['input_core_sha256'],steps=[dict(kind='physical',package=chosen)])
   packet=write(root/'plan.json',plan);invoke(compiler,'emit-plan',source,packet,'--target','javascript','-o',root/'module.mjs')
   invoke(compiler,'build',source,'--target','javascript','-o',root/'baseline.mjs')
   (root/'check.mjs').write_text("import assert from 'node:assert/strict';\nimport * as chosen from './module.mjs';import * as baseline from './baseline.mjs';\nconst outcome=run=>{try{return {value:run()};}catch(error){return {name:error.name,message:error.message};}};\nfor(const compact of [false,true]){\n const codec=compact?baseline.valueCodecs.echo.arguments.compact():baseline.valueCodecs.echo.arguments;\n const bytes=codec.encode({rows:[1,2,4294967295]});\n const call=compact?'callCompact':'callBinary';\n assert.deepEqual(chosen[call]('echo',bytes),baseline[call]('echo',bytes));\n for(let i=0;i<bytes.length;i++){const corrupt=bytes.slice();corrupt[i]^=255;assert.deepEqual(outcome(()=>chosen[call]('echo',corrupt)),outcome(()=>baseline[call]('echo',corrupt)));}\n for(let end=0;end<bytes.length;end++)assert.deepEqual(outcome(()=>chosen[call]('echo',bytes.subarray(0,end))),outcome(()=>baseline[call]('echo',bytes.subarray(0,end))));\n}\n")
   checked=subprocess.run(['node',str(root/'check.mjs')],capture_output=True,text=True)
   self.assertEqual(checked.returncode,0,checked.stderr)

   for target in ['rust','rust-wasm','wgpu','webgpu']:
    with self.assertRaisesRegex(ValueError,'boundary readers'):invoke(compiler,'emit-plan',source,packet,'--target',target,'-o',root/target)
