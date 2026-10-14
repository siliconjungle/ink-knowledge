"""A stopping-fold simulation needs both universal transition and stop facts."""
import copy,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry

class UntilProjection(unittest.TestCase):
 def test_indexed_loop_projection_requires_step_and_stop(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));store=Store(root/'knowledge/libraries/proofs/until-projection');lid=next(iter(store.members()));original=store.object(lid)
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);source=d/'subject.ink';source.write_text('module subject;fn add(x:u32)->u32{return x+1;}');core=d/'core.json'
   result=subprocess.run([compiler,'emit-core',source,'-o',core],capture_output=True,text=True,timeout=180);self.assertEqual(result.returncode,0,result.stderr[-1500:])
   for label,removed in [('complete',None),('step',0),('stop',1)]:
    theorem=dict(copy.deepcopy(original['payload']),schema=1,semantics=original['semantics'],dependencies=original['dependencies'])
    if removed is not None:theorem['assumptions'].pop(removed)
    obj=semantic_entry(theorem);ident=identity(obj);trial=Store.publish(d/label,[obj]);view=d/(label+'.json');view.write_bytes(canonical(trial.bundle([ident])))
    result=subprocess.run([compiler,'knowledge-check',core,view],capture_output=True,text=True,timeout=180)
    self.assertEqual(result.returncode==0,removed is None,label+' '+result.stderr[-2000:])
    if removed is not None:self.assertIn('assumption',result.stderr.lower())

if __name__=='__main__':unittest.main()
