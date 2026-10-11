import copy,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from producers.state_laws import library
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
class StateLaws(unittest.TestCase):
 def test_checked_frames_grouping_and_false_intermediate_rejected(self):
  objects,names=library()
  with tempfile.TemporaryDirectory() as tmp:
   d=Path(tmp);source=d/'source.ink';core=d/'core.json';view=d/'view.json';source.write_text('module state_laws; pub fn identity(x:u64)->u64{return x;}')
   def run(*args):return subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True)
   self.assertEqual(run('emit-core',source,'-o',core).returncode,0)
   store=Store.publish(d/'good',objects.values(),names);view.write_bytes(canonical(store.bundle(list(objects)))+b'\n');r=run('knowledge-check',core,view);self.assertEqual(r.returncode,0,r.stderr)
   bad=copy.deepcopy(objects[names['grouped_preserves_intermediate_and_final']]);goal=bad['payload']['declaration']['Theorem'];goal['to']['Construct']['arguments'][0]=goal['to']['Construct']['arguments'][1]
   forged={**objects,identity(bad):bad};store=Store.publish(d/'bad',forged.values());view.write_bytes(canonical(store.bundle([identity(bad)]))+b'\n');r=run('knowledge-check',core,view);self.assertNotEqual(r.returncode,0);self.assertNotIn('hash mismatch',r.stderr)
if __name__=='__main__':unittest.main()
