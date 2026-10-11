"""The database proposes; the compiler checks every induction and application."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,semantic_entry,identity,canonical
from producers.fold_until_laws import named_laws,specialize
from producers.semantic_laws import value,term
from ink_planner.semantic_search import match
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
SOURCE='''module Universal;
fn first(xs:List<u32>,z:u32,k:u32)->u32{return foldr(xs,z,fn(x)=>fn(a)=>choose(x>k,x,a));}
fn nested(xs:List<u32>,z:u32,k:u32)->u32{return foldr(xs,z,fn(x)=>fn(a)=>choose(x==k,z,choose(x>k,choose(x==z,a,x+1),a)));}
fn negative_value(xs:List<u32>,z:u32,k:u32)->u32{return foldr(xs,z,fn(x)=>fn(a)=>choose(x>k,x+a,a));}
fn negative_predicate(xs:List<u32>,z:u32,k:u32)->u32{return foldr(xs,z,fn(x)=>fn(a)=>choose(a>k,x,a));}
fn nested_capture(xs:List<u32>,ys:List<u32>,z:u32,k:u32)->u32{return foldr(xs,z,fn(x)=>fn(a)=>choose(sum(ys.map(fn(a)=>a))>k,sum(ys.map(fn(a)=>a+x)),a));}
fn hidden_capture(xs:List<u32>,ys:List<u32>,z:u32,k:u32)->u32{return foldr(xs,z,fn(x)=>fn(a)=>choose(x>k,sum(ys.map(fn(y)=>y+a)),a));}
fn mixed(xs:List<u32>,z:String,k:u32)->String{return foldr(xs,z,fn(x)=>fn(a)=>choose(x>k,"found",a));}
'''
class FoldUntilLaws(unittest.TestCase):
 def run_command(self,*args,ok=True):
  r=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True)
  if ok:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def test_induction_and_application_then_literal_execution(self):
  with tempfile.TemporaryDirectory()as d:
   d=Path(d);src=d/'source.ink';src.write_text(SOURCE);core=d/'core.json';subject=d/'subject.json'
   self.run_command('emit-core',src,'-o',core);self.run_command('emit-semantic',core,'--core','-o',subject)
   subject=json.loads(subject.read_text());rows=specialize(subject)
   self.assertEqual({n.split('_early_exit')[0].rstrip('_')for n,_ in rows if n.endswith('_early_exit')},{'first','nested','nested_capture','mixed'})
   all_rows=named_laws()+rows;st=Store.publish(d/'knowledge',[semantic_entry(l)for _,l in all_rows]);view=d/'view.json';view.write_bytes(canonical(st.bundle(list(st.members())))+b'\n')
   self.run_command('knowledge-check',core,view)
   apps=[]
   for name,body in subject['functions'].items():
    for _,l in rows:
     bindings={}
     if match(l['from'],body,l['params'],bindings)and set(bindings)==set(l['params']):
      apps.append(dict(function=name,path=[],law=identity(semantic_entry(l)),arguments=bindings,premises=[]));break
   self.assertEqual({a['function']for a in apps},{'first','nested','nested_capture','mixed'})
   package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=st.bundle([a['law']for a in apps]),applications=apps)
   selection=d/'selection.json';selection.write_bytes(canonical(package)+b'\n')
   self.run_command('check-selection',core,selection)
   js=d/'selected.mjs';self.run_command('build',core,'--core','--selection',selection,'--target','javascript','-o',js)
   self.assertIn('break;',js.read_text())
   args=d/'args.json'
   for fn,a in [('first',[[0,1,9],7,1]),('nested',[[1,9],1,1]),('mixed',[[1,9],'default',3])]:
    args.write_text(json.dumps(a));baseline=self.run_command('run',core,fn,args,'--core').stdout;selected=self.run_command('run',core,fn,args,'--core','--selection',selection).stdout;self.assertEqual(json.loads(baseline),json.loads(selected))
   run=d/'run.mjs';run.write_text("import assert from'node:assert/strict';import{functions}from'./selected.mjs';let reads=0;const xs=[0,1,9];xs.forEach((x,i)=>Object.defineProperty(xs,i,{get(){reads++;return x;}}));assert.equal(functions.first(xs,7,1),9);assert.equal(reads,3);reads=0;assert.equal(functions.first(xs,7,0),1);assert.equal(reads,2);assert.equal(functions.mixed([1,9],'default',3),'found');assert.equal(functions.nested([1,9],1,1),1);")
   r=subprocess.run(['node',str(run)],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
   # Rehashed false proof bytes receive no authority.
   bad=copy.deepcopy(rows[0][1]);bad['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']=term(value('Bool'),{'Bool':True})
   forged=Store.publish(d/'bad',[semantic_entry(bad)]);view.write_bytes(canonical(forged.bundle(list(forged.members())))+b'\n');r=self.run_command('knowledge-check',core,view,ok=False);self.assertNotEqual(r.returncode,0);self.assertNotIn('hash mismatch',r.stderr)
if __name__=='__main__':unittest.main()
