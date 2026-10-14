"""Complete portable map-frame closures must replay with their exact source."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
class ParentMapFrames(unittest.TestCase):
 def test_target_batch_and_traversal_component_closures(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  for name in ['parent-target-map-frames','parent-batch-map-frames','parent-traversal-step-frames','parent-traversal-loop-frames','parent-original-traversal-frames','parent-range-step-frames','parent-range-loop-frames','parent-preparation-map-frames','parent-resolver-map-frames']:
   directory=root/'knowledge/libraries/proofs'/name;store=Store(directory);ids=list(json.loads((directory/'store/names.json').read_text()).values())
   with tempfile.TemporaryDirectory()as temp:
    view=Path(temp)/'view.json';view.write_bytes(canonical(store.bundle(ids)));r=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,name+' '+r.stderr[-1800:]);self.assertEqual(json.loads(r.stdout)['status'],'checked')
 def test_rehashed_erased_parent_map_is_rejected(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  directory=root/'knowledge/libraries/proofs/parent-range-loop-frames';store=Store(directory)
  names=json.loads((directory/'store/names.json').read_text());lid=names['source/ordinary_added_step_loop_ends'];obj=store.object(lid)
  theorem=dict(copy.deepcopy(obj['payload']),schema=1,semantics=obj['semantics'],dependencies=obj['dependencies'])
  # Retain a well-typed map, but erase every entry: changing and rehashing the
  # conclusion must not retain authority from the genuine preservation proof.
  theorem['to']={'sort':theorem['to']['sort'],'node':{'Op':['local:map-empty',[]]}}
  bad=semantic_entry(theorem)
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);forged=Store.publish(d/'false',[store.object(i)for i in store.members()if i!=lid]+[bad]);view=d/'view.json';view.write_bytes(canonical(forged.bundle([identity(bad)])))
   result=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120)
   self.assertNotEqual(result.returncode,0);self.assertTrue('exact goal' in result.stderr or 'normal forms differ' in result.stderr,result.stderr[-1800:])
if __name__=='__main__':unittest.main()
