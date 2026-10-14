import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.definitional_roundtrips import propose
from producers.semantic_laws import op,value,var

class DefinitionalRoundtrips(unittest.TestCase):
 def test_complete_record_inverse_replays_and_field_mutation_is_rejected(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source='''module codec;record Stored{left:List<u32>,right:List<u32>,}record Owned{left:Buffer<u32>,right:Buffer<u32>,}
fn load(s:Stored)->Owned{return Owned{left:buffer(s.left),right:buffer(s.right)};}
fn store(s:Owned)->Stored{return Stored{left:s.left.freeze(),right:s.right.freeze()};}
fn roundtrip(s:Stored)->Stored{return store(load(s));}'''
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);path=d/'codec.ink';path.write_text(source)
   for command,name in [('emit-core','core'),('emit-semantic','semantic')]:
    r=subprocess.run([compiler,command,path,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
   core=json.loads((d/'core.json').read_text());subject=json.loads((d/'semantic.json').read_text());law=propose(core,subject,'roundtrip')
   for bad in [False,True]:
    candidate=copy.deepcopy(law)
    if bad:
     s=var(value({'Named':'Stored'}),'s');xs=value({'List':'U32'})
     candidate['to']=op(s['sort'],'record:Stored',op(xs,'field:right',s),op(xs,'field:left',s))
    obj=semantic_entry(candidate);store=Store.publish(d/str(bad),[obj]);view=d/(str(bad)+'.json');view.write_bytes(canonical(store.bundle([identity(obj)])))
    r=subprocess.run([compiler,'knowledge-check',d/'core.json',view],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode==0,not bad,r.stderr[-2000:])

if __name__=='__main__':unittest.main()
