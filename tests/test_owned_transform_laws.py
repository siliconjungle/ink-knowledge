"""Owned implementation proposals need ordinary equality admission."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,semantic_entry
from producers.owned_transform_laws import named_laws,specialize
from ink_knowledge.proposals import generate
from producers.definition_context28 import bind
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
class OwnedTransformLaws(unittest.TestCase):
 def test_general_carriers_and_false_compaction(self):
  with tempfile.TemporaryDirectory()as directory:
   d=Path(directory);source=d/'source.ink';core=d/'core.json';subject=d/'subject.json';view=d/'view.json'
   source.write_text('module owners;record Row{x:u32,}fn select_rows(xs:List<Row>)->List<Row>{return xs.filter(fn(r)=>r.x>0);}fn words(xs:List<u32>)->List<u32>{return xs.filter(fn(x)=>x>2);}fn chain(xs:List<u32>)->List<u32>{return xs.filter(fn(x)=>x>2).map(fn(x)=>x+1).scan();}')
   def run(*args):return subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True)
   for args in [('emit-core',source,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
    r=run(*args);self.assertEqual(r.returncode,0,r.stderr)
   rows=named_laws();self.assertEqual(len(rows),28)
   subject_value=json.loads(subject.read_text());core_value=json.loads(core.read_text())
   generated=specialize(subject_value);self.assertEqual(len(generated),5)
   pipeline=dict(generated)['chain_owned_']['to']
   def buffers(v):
    if isinstance(v,dict):return int(v.get('node',{}).get('Op',[None])[0]=='call:buffer')+sum(buffers(x)for x in v.values())
    return sum(buffers(x)for x in v)if isinstance(v,list)else 0
   self.assertEqual(buffers(pipeline),1)
   self.assertEqual(pipeline['node']['Op'][1][0]['node']['Op'][0],'method:scan')
   generated=[(name,bind(law,core_value,subject_value))for name,law in generated]
   discovered,_=generate(subject_value,core_value)
   self.assertTrue(any(o['payload'].get('definition_context',{}).get('records')for o in discovered.values()))
   st=Store.publish(d/'knowledge',[semantic_entry(l)for _,l in rows+generated]);view.write_bytes(canonical(st.bundle(list(st.members())))+b'\n')
   r=run('knowledge-check',core,view);self.assertEqual(r.returncode,0,r.stderr)
   # A predicate cannot be silently replaced by always true, even with new hashes.
   bad=json.loads(json.dumps(dict(generated)['words_owned_']))
   predicate=bad['to']['node']['Op'][1][0]['node']['Op'][1][1]
   predicate['node']['Lambda']['node']={'Bool':True}
   st=Store.publish(d/'false',[semantic_entry(bad)]);view.write_bytes(canonical(st.bundle(list(st.members())))+b'\n')
   r=run('knowledge-check',core,view);self.assertNotEqual(r.returncode,0);self.assertNotIn('hash mismatch',r.stderr)
if __name__=='__main__':unittest.main()
