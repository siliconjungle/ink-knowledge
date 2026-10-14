"""Composed source observer proof and a canonical false-root rejection."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
class BlockedFrames(unittest.TestCase):
 def test_composed_search_preserves_index_and_rejects_false_root(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));directory=root/'knowledge/libraries/proofs'/getattr(self,'proof_directory','blocked-interval-search-frame');store=Store(directory);lid=getattr(self,'proof_law','9f2512b40f8c887a24d52913f260ab123cd33b75a3a3cecb6877486528936b07')
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);view=d/'view.json';view.write_bytes(canonical(store.bundle([lid])));r=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1800:])
   o=store.object(lid);t=dict(copy.deepcopy(o['payload']),schema=1,semantics=o['semantics'],dependencies=o['dependencies']);base=t['to'];core=json.loads((directory/'checked-source.json').read_text());fields=core['program']['records'][base['sort']['Value']['Named']];args=[{'sort':{'Value':ty},'node':{'Word':0}if n=='root'else{'Op':['field:'+n,[base]]}}for n,ty in fields];t['to']={'sort':base['sort'],'node':{'Op':['record:'+base['sort']['Value']['Named'],args]}};bad=semantic_entry(t);s=Store.publish(d/'false',[store.object(i)for i in store.members()if i!=lid]+[bad]);view.write_bytes(canonical(s.bundle([identity(bad)])));r=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120);self.assertNotEqual(r.returncode,0);self.assertTrue('semantic normal forms differ'in r.stderr or 'fixed computation does not establish exact goal'in r.stderr,r.stderr)
class BlockedLoopFrames(BlockedFrames):
 proof_directory='blocked-interval-tree-search-frame'
 proof_law='cd62ef61ce745ed3baca46ebf20656354c2ad97d0192cd184a3ea5b9af38ee6c'
if __name__=='__main__':unittest.main()
