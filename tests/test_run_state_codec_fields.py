import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
class RunStateCodecFields(unittest.TestCase):
 def test_portable_fields_and_false_root(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  proof=root/'knowledge/libraries/proofs/run-state-codec-fields';store=Store(proof);names=json.loads((proof/'store/names.json').read_text());core=proof/'checked-source.json'
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp);view=d/'positive.json';view.write_bytes(canonical(store.bundle(names.values())))
   r=subprocess.run([compiler,'knowledge-check',core,view],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
   obj=copy.deepcopy(store.object(names['run-state/roundtrip/root']));obj['payload']['to']={'sort':{'Value':'U32'},'node':{'Word':0}};obj['payload']['proof']='Unfold';obj=semantic_entry(dict(obj['payload'],schema=1,semantics=obj['semantics'],dependencies=obj['dependencies']))
   false=d/'false';bad=Store.publish(false,[obj]);view=d/'false.json';view.write_bytes(canonical(bad.bundle([identity(obj)])))
   r=subprocess.run([compiler,'knowledge-check',core,view],capture_output=True,text=True,timeout=120);self.assertNotEqual(r.returncode,0);self.assertNotIn('unknown variant',r.stderr);self.assertNotIn('interface differs',r.stderr)
if __name__=='__main__':unittest.main()
