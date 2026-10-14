"""Resolver carrier commutation replays and rejects discarded parent lists."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
class ParentResolution(unittest.TestCase):
 def test_resolution_carrier_bridge_and_rehashed_empty_list(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));directory=root/'knowledge/libraries/proofs/parent-resolution-fold';store=Store(directory);lid=json.loads((directory/'store/names.json').read_text())['source/fold_commutation']
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);view=d/'view.json';view.write_bytes(canonical(store.bundle([lid])));r=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1500:])
   o=store.object(lid);t=dict(copy.deepcopy(o['payload']),schema=1,semantics=o['semantics'],dependencies=o['dependencies']);t['to']=copy.deepcopy(t['from']);t['to']['node']['Op'][1][0]['node']['Op'][1][0]={'sort':t['params']['items'],'node':'Nil'};bad=semantic_entry(t);stage=Store.publish(d/'false',[bad]);view.write_bytes(canonical(stage.bundle([identity(bad)])));r=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120);self.assertNotEqual(r.returncode,0);self.assertIn('induction schema does not establish exact goal',r.stderr)
if __name__=='__main__':unittest.main()
