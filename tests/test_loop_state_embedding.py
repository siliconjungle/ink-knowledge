"""Source loop narrowing is general, proof checked, and fails closed on changes."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.loop_state_embedding import propose

SOURCE='''module loop_state;
record Big{data:Buffer<u32>,index:u32,total:u32,}
record Small{index:u32,total:u32,}
fn step(s:Big)->Big{let item=s.data.at_or(s.index,0);return Big{data:s.data,index:s.index+1,total:s.total+item};}
fn small(s:Small,item:u32)->Small{return Small{index:s.index+1,total:s.total+item};}
fn original(data:List<u32>,count:u32)->Big{
 return repeat_until(count,Big{data:buffer(data),index:0,total:0},fn(s)=>s.index>=count,fn(i,s)=>step(s));
}
fn reduced(data:List<u32>,count:u32)->Big{
 let data=buffer(data);let s=repeat_until(count,Small{index:0,total:0},fn(s)=>s.index>=count,fn(i,s)=>small(s,data.at_or(s.index,0)));
 return Big{data:data,index:s.index,total:s.total};
}
'''

class LoopStateEmbedding(unittest.TestCase):
 def test_general_source_simulation_and_rehashed_mutation_rejection(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  parent=Store(root/'knowledge/libraries/proofs/until-embedding');key=json.loads((parent.root/'store/names.json').read_text())['until_embedding']
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);source=d/'source.ink';source.write_text(SOURCE);corefile=d/'core.json';subjectfile=d/'subject.json'
   for command,path in [('emit-core',corefile),('emit-semantic',subjectfile)]:
    r=subprocess.run([compiler,command,source,'-o',path],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1500:])
   core=json.loads(corefile.read_bytes());subject=json.loads(subjectfile.read_bytes());law=propose(core,subject,'original','reduced',key)
   def replay(label,theorem):
    obj=semantic_entry(theorem);entries={**parent.bundle([key])['objects'],identity(obj):obj};trial=Store.publish(d/label,list(entries.values()));view=d/(label+'.json');view.write_bytes(canonical(trial.bundle([identity(obj)])))
    return subprocess.run([compiler,'knowledge-check',corefile,view],capture_output=True,text=True,timeout=120)
   r=replay('valid',law);self.assertEqual(r.returncode,0,r.stderr[-2000:])
   changed=copy.deepcopy(law)
   # Recomputing the definition-context hashes cannot make a different
   # transition satisfy an old proof or the source image.
   definitions=changed['definition_context']['definitions'];definition=definitions['small']['definition'];definition['body']=subject['functions']['step'];definitions['small']['sha256']=identity(definition)
   r=replay('changed-definition',changed);self.assertNotEqual(r.returncode,0,r.stdout)
   source.write_text(SOURCE.replace('fn small(s:Small,item:u32)->Small{return Small{index:s.index+1,total:s.total+item};}',
    'fn small(s:Small,item:u32)->Small{return Small{index:s.index+1,total:s.total+item+1};}'))
   for command,path in [('emit-core',corefile),('emit-semantic',subjectfile)]:
    r=subprocess.run([compiler,command,source,'-o',path],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1500:])
   with self.assertRaisesRegex(ValueError,'callback does not preserve'):
    propose(json.loads(corefile.read_bytes()),json.loads(subjectfile.read_bytes()),'original','reduced',key)

if __name__=='__main__':unittest.main()
