"""Source frame proofs reject mutations, including with rehashed contexts."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.definitional_frames import propose
from producers.definition_context28 import bind

class DefinitionalFrames(unittest.TestCase):
 def test_callback_preservation_and_changed_source_rejection(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  frame_root=root/'knowledge/libraries/proofs/until-frame';frame=Store(frame_root)
  key=json.loads((frame_root/'store/names.json').read_text())['until_frame']
  source='''module frames;record Cursor{data:List<u32>,index:u32,}
fn observe(data:List<u32>,count:u32,increment:u32)->List<u32>{
 let s=repeat_until(count,Cursor{data:data,index:0},fn(s)=>s.index>=9,
 fn(i,s)=>choose(i==0,Cursor{data:s.data,index:s.index+increment},Cursor{data:s.data,index:s.index+1}));return s.data;}
'''
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary)
   def run(*args):return subprocess.run([compiler,*map(str,args)],capture_output=True,text=True,timeout=120)
   def elaborate(label,text):
    path=d/(label+'.ink');path.write_text(text);core=d/(label+'.core.json');subject=d/(label+'.semantic.json')
    for args in [('emit-core',path,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
     r=run(*args);self.assertEqual(r.returncode,0,r.stderr[-2000:])
    return core,json.loads(core.read_text()),json.loads(subject.read_text())
   def check(label,path,proposal):
    obj=semantic_entry(proposal);store=Store.publish(d/label,[frame.object(key),obj]);view=d/(label+'.view.json');view.write_bytes(canonical(store.bundle([identity(obj)])))
    return run('knowledge-check',path,view)
   path,core,subject=elaborate('valid',source);good=propose(core,subject,'observe','data',key)
   r=check('checked',path,good);self.assertEqual(r.returncode,0,r.stderr[-2000:])
   bad_path,bad_core,bad_subject=elaborate('mutated',source.replace('data:s.data,index:s.index+1','data:s.data.concat([i]),index:s.index+1'))
   with self.assertRaises(ValueError):propose(bad_core,bad_subject,'observe','data',key)
   # Rebind all content identities to the changed, well-typed source. The
   # original proof still must fail; hashes cannot authorize its conclusion.
   forged=bind(good,bad_core,bad_subject,['observe']);r=check('forged',bad_path,forged)
   self.assertNotEqual(r.returncode,0,r.stdout)

if __name__=='__main__':unittest.main()
