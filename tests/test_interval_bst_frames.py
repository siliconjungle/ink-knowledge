"""Source observer proofs replay independently of benchmark or planner receipts."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry

class IntervalFrames(unittest.TestCase):
 def test_entire_index_frame_and_rehashed_false_root(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source=root/'knowledge/libraries/proofs/interval-bst-index-frame';store=Store(source)
  lid='9a6b89d8610b6db9824acfc8f031d8b4478c93285b90764931791a21708a1819'
  with tempfile.TemporaryDirectory()as directory:
   d=Path(directory);view=d/'valid.json';view.write_bytes(canonical(store.bundle([lid])))
   result=subprocess.run([compiler,'knowledge-check',source/'checked-source.json',view],capture_output=True,text=True,timeout=120)
   self.assertEqual(result.returncode,0,result.stderr[-1500:])
   obj=store.object(lid);theorem=dict(copy.deepcopy(obj['payload']),schema=1,semantics=obj['semantics'],dependencies=obj['dependencies'])
   base=theorem['to'];core=json.loads((source/'checked-source.json').read_text());schema=core['program']['records'][base['sort']['Value']['Named']]
   fields=[{'sort':{'Value':ty},'node':{'Word':0}if name=='root'else{'Op':['field:'+name,[base]]}}for name,ty in schema]
   theorem['to']={'sort':base['sort'],'node':{'Op':['record:'+base['sort']['Value']['Named'],fields]}};bad=semantic_entry(theorem)
   staged=Store.publish(d/'false',[store.object(i)for i in store.members()if i!=lid]+[bad]);view=d/'false.json';view.write_bytes(canonical(staged.bundle([identity(bad)])))
   result=subprocess.run([compiler,'knowledge-check',source/'checked-source.json',view],capture_output=True,text=True,timeout=120)
   self.assertNotEqual(result.returncode,0);self.assertIn('semantic normal forms differ',result.stderr)

if __name__=='__main__':unittest.main()
