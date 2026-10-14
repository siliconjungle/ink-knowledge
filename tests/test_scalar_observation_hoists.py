"""Replay general observation scheduling proofs, including nested lexical scope."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path[:0]=[str(ROOT/'knowledge'),str(ROOT/'planner')]
from ink_knowledge import Store,canonical,semantic_entry,identity
from producers.scalar_observation_hoists import propose_terms

SOURCE='''module observation_tests;
record Row{id:u32,payload:List<u32>,parents:List<u32>,}
record Out{rows:Buffer<Row>,last:u32,}
record Saved{rows:List<Row>,last:u32,}
fn append(rows:Buffer<Row>,row:Row)->Out{return Out{rows:rows.push(row),last:row.id+length(row.payload)};}
fn already(rows:Buffer<Row>,row:Row)->Out{let last=row.id+length(row.payload);return Out{rows:rows.push(row),last:last};}
fn none()->List<Row>{return [];}
fn nested(rows:List<Row>)->List<Saved>{return rows.map(fn(row)=>Saved{rows:buffer(none()).push(row).freeze(),last:row.id+length(row.payload)});}
fn run(payload:List<u32>)->List<u32>{let out=append(Buffer.empty(),Row{id:7,payload:payload,parents:[]});return [out.last,out.rows.len()];}
'''

class ObservationHoists(unittest.TestCase):
 def test_replay_hygiene_and_false_equality_rejection(self):
  compiler=Path(os.environ['INK_COMPILER']).resolve()
  with tempfile.TemporaryDirectory()as tmp:
   p=Path(tmp);source=p/'source.ink';source.write_text(SOURCE)
   def invoke(*args):return subprocess.run([compiler,*map(str,args)],capture_output=True,text=True,timeout=120)
   for command,name in [('emit-core','core.json'),('emit-semantic','semantic.json')]:
    r=invoke(command,source,'-o',p/name);self.assertEqual(r.returncode,0,r.stderr)
   core=json.loads((p/'core.json').read_text());subject=json.loads((p/'semantic.json').read_text());sid=json.loads(invoke('check-core',p/'core.json').stdout)['core_sha256'];rows=propose_terms(core,subject,16)
   names={r['application']['function']for r in rows};self.assertTrue({'append','nested'}<=names);self.assertNotIn('already',names)
   for i,row in enumerate(rows):
    obj=semantic_entry(row['law']);lid=identity(obj);store=Store.publish(p/f'proof-{i}',[obj]);view=store.bundle([lid]);vp=p/f'view-{i}.json';vp.write_bytes(canonical(view));r=invoke('knowledge-check',p/'core.json',vp);self.assertEqual(r.returncode,0,r.stderr)
    packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=sid,knowledge=view,applications=[dict(row['application'],law=lid)]);plan=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=sid,steps=[dict(kind='rewrite',package=packet)]);pp=p/f'plan-{i}.json';pp.write_bytes(canonical(plan));r=invoke('check-plan',p/'core.json',pp,'--core','--target','rust');self.assertEqual(r.returncode,0,r.stderr)
   bad=copy.deepcopy(rows[0]['law']);observation=bad['to']['node']['Op'][1][1];observation['node']={'Word':0};obj=semantic_entry(bad);lid=identity(obj);store=Store.publish(p/'counterfeit',[obj]);vp=p/'bad.json';vp.write_bytes(canonical(store.bundle([lid])));r=invoke('knowledge-check',p/'core.json',vp);self.assertNotEqual(r.returncode,0,'a different scalar observation cannot be justified by beta equality')

if __name__=='__main__':unittest.main()
