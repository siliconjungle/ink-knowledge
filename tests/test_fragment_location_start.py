import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
class FragmentLocationStart(unittest.TestCase):
 def test_guarded_fragment_and_dropped_arithmetic_dependency(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  proof=root/'knowledge/libraries/proofs/fragment-location-start';store=Store(proof);names=json.loads((proof/'store/names.json').read_text());core=proof/'checked-source.json'
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp);view=d/'positive.json';view.write_bytes(canonical(store.bundle(names.values())))
   r=subprocess.run([compiler,'knowledge-check',core,view],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
   obj=copy.deepcopy(store.object(names['source/fragment_start']));obj['dependencies']=[];bad=Store.publish(d/'false',[obj]);view=d/'false.json';view.write_bytes(canonical(bad.bundle([identity(obj)])))
   r=subprocess.run([compiler,'knowledge-check',core,view],capture_output=True,text=True,timeout=120);self.assertNotEqual(r.returncode,0)
if __name__=='__main__':unittest.main()
