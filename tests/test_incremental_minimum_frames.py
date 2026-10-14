"""Minimum-update observer proofs retain their precise component boundaries."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
class MinimumFrames(unittest.TestCase):
 def test_all_observers_and_rehashed_false_root(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));directory=root/'knowledge/libraries/proofs/incremental-minimum-frames';store=Store(directory);names=json.loads((directory/'store/names.json').read_text());ids=list(names.values())
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);view=d/'view.json';view.write_bytes(canonical(store.bundle(ids)));r=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1800:])
   lid=names['source/minimum_preserves_root'];o=store.object(lid);t=dict(copy.deepcopy(o['payload']),schema=1,semantics=o['semantics'],dependencies=o['dependencies']);t['to']={'sort':t['to']['sort'],'node':{'Word':0}};bad=semantic_entry(t);s=Store.publish(d/'false',[store.object(i)for i in store.members()if i!=lid]+[bad]);view.write_bytes(canonical(s.bundle([identity(bad)])));r=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120);self.assertNotEqual(r.returncode,0);self.assertIn('fixed computation does not establish exact goal',r.stderr)
if __name__=='__main__':unittest.main()
