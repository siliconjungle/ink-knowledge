import json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical

class GeneratedProposals(unittest.TestCase):
 def test_planner_generates_checked_fold_and_unfolding_closures(self):
  root=Path(__file__).resolve().parents[2];compiler=root/'target/debug/ink'
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);st=Store.publish(d/'knowledge',[])
   source=d/'source.ink';source.write_text('module proof;fn leaf(x:u32)->u32{return x+1;}fn first(xs:List<u32>,z:u32,k:u32)->u32{return foldr(xs,z,fn(x)=>fn(a)=>choose(x>k,leaf(x),a));}fn helper(x:u32)->u32{return leaf(x);}')
   core=d/'core.json';selection=d/'selection.json';model=d/'costs.json'
   def run(*args):
    r=subprocess.run([str(a)for a in args],cwd=root,capture_output=True,text=True)
    self.assertEqual(r.returncode,0,r.stderr);return r
   run(compiler,'emit-core',source,'-o',core)
   model.write_text(json.dumps({'schema':1,'operation_costs':{'call:foldr':1000,'call:fold_until':1,'call:leaf':100}}))
   env=dict(os.environ,PYTHONPATH=str(root/'knowledge')+os.pathsep+str(root/'planner'))
   r=subprocess.run(['python3','-m','ink_planner.semantic_search','--compiler',str(compiler),'--core',str(core),'--snapshot',str(d/'knowledge/store/snapshot.json'),'--knowledge-root',str(d/'knowledge'),'--cost-model',str(model),'-o',str(selection),'--budget','16','--rounds','4'],cwd=root,env=env,capture_output=True,text=True)
   self.assertEqual(r.returncode,0,r.stderr)
   report=json.loads(r.stdout);self.assertEqual(report['database']['source_snapshot_sha256'],st.snapshot_id)
   self.assertTrue(report['database']['producers']);self.assertNotEqual(report['database']['snapshot_sha256'],st.snapshot_id)
   package=json.loads(selection.read_text());self.assertTrue(package['applications'])
   run(compiler,'check-selection',core,selection)
   emitted=d/'out.mjs';run(compiler,'build',core,'--core','--selection',selection,'--target','javascript','-o',emitted)
   self.assertIn('break;',emitted.read_text())
   check=d/'check.mjs';check.write_text("import assert from'node:assert/strict';import{functions}from'./out.mjs';assert.equal(functions.first([1,9,3],7,4),10);assert.equal(functions.helper(8),9);")
   run('node',check)
   self.assertEqual(Store(d/'knowledge').snapshot_id,st.snapshot_id)
