"""Small helper discovery still requires complete source equality replay."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from producers.small_inline import candidates,propose

SOURCE='''module example;
record Owner{a:List<u32>,b:List<u32>,c:List<u32>,tag:u32,}
fn observed(s:Owner,amount:u32)->Owner{return Owner{a:s.a,b:s.b,c:s.c,tag:s.tag+amount};}
fn main(s:Owner,amount:u32)->u32{return observed(s,amount).tag+observed(s,amount+1).tag;}
fn callback(xs:List<Owner>,amount:u32)->List<u32>{return xs.map(fn(s)=>observed(s,amount).tag);}
record Mutable{left:Buffer<u32>,right:Buffer<u32>,tag:u32,pad:u32,}
record Tagged{owner:Mutable,value:u32,}
fn reading(s:Mutable)->Tagged{let value=s.tag;return Tagged{owner:s,value:value};}
fn owned_sum(xs:List<u32>)->u32{
 let owner=Mutable{left:buffer(xs),right:Buffer.empty(),tag:17,pad:0};
 let tagged=reading(owner);return tagged.value;
}
'''

class SmallInline(unittest.TestCase):
 def test_helpers_capture_binders_and_rehashed_false_body(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);source=d/'source.ink';source.write_text(SOURCE);core=d/'core.json';semantic=d/'semantic.json'
   def run(*args):return subprocess.run(list(map(str,[compiler,*args])),capture_output=True,text=True,timeout=180)
   for command,out in [('emit-core',core),('emit-semantic',semantic)]:
    result=run(command,source,'-o',out);self.assertEqual(result.returncode,0,result.stderr[-2000:])
   checked=json.loads(core.read_bytes());subject=json.loads(semantic.read_bytes());rows=list(candidates(checked,subject))
   self.assertEqual({x['name']for x in rows},{'observed','reading'})
   self.assertEqual(next(candidates(checked,subject,limit=1))['name'],'reading')
   self.assertEqual(next(candidates(checked,subject,limit=1,frequencies={'call:observed':1000,'call:reading':0}))['name'],'observed')
   self.assertFalse(list(candidates(checked,subject,limit=0)))
   self.assertFalse(list(candidates(checked,subject,max_body=1)))
   self.assertFalse(list(candidates(checked,subject,max_applications=0)))
   self.assertFalse(list(candidates(checked,subject,min_body=0)))
   self.assertFalse(list(candidates(checked,subject,min_body=65,max_body=64)))
   for row in rows:
    store=Store.publish(d/row['name'],[row['object']]);view=store.bundle([row['law']]);packet=d/(row['name']+'.json')
    packet.write_bytes(canonical(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=view,applications=row['applications'])))
    result=run('check-selection',core,packet);self.assertEqual(result.returncode,0,row['name']+' '+result.stderr[-3000:])
   row=next(x for x in rows if x['name']=='observed');false=copy.deepcopy(row['object'])
   false['payload']['to']=copy.deepcopy(false['payload']['from']['node']['Op'][1][0]);lid=identity(false)
   store=Store.publish(d/'false',[false]);packet=d/'false.json'
   applications=[dict(a,law=lid)for a in row['applications']]
   packet.write_bytes(canonical(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=store.bundle([lid]),applications=applications)))
   result=run('check-selection',core,packet);self.assertNotEqual(result.returncode,0)
   self.assertIn('normal',result.stderr.lower())
   base=Store.publish(d/'composition',[])
   context=dict(core=checked,source=subject['input_core_sha256'],compiler=str(compiler),knowledge_root=str(base.root),knowledge_snapshot=base.snapshot_id,emit_target='rust',check_timeout=120)
   rows=list(propose(context,limit=1,physical_strategies=[dict(tables='ordered',buffers='direct',borrow=False,targets=['rust']),dict(tables='ordered',buffers='direct',borrow=True,targets=['rust'])]))
   paired=[r for r in rows if r['status']=='proposal'and 'steps'in r]
   self.assertEqual(len(paired),2,rows)
   for index,row in enumerate(paired):
    self.assertEqual([s['kind']for s in row['steps']],['rewrite','physical'])
    self.assertNotEqual(row['steps'][1]['package']['input_core_sha256'],context['source'])
    packet=d/f'composition-{index}.json';packet.write_bytes(canonical(dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=context['source'],steps=row['steps'])))
    result=run('check-plan',core,packet,'--core');self.assertEqual(result.returncode,0,result.stderr[-2500:])
   rows=list(propose(context,limit=1,scoped_strategies=['all-observations']))
   paired=[r for r in rows if r['status']=='proposal'and 'steps'in r]
   self.assertEqual(len(paired),1,rows)
   row=paired[0];fresh=row['steps'][1]['package']
   self.assertNotEqual(fresh['input_core_sha256'],context['source'])
   self.assertTrue(fresh['borrow_reads'])
   packet=d/'scoped-composition.json';packet.write_bytes(canonical(dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=context['source'],steps=row['steps'])))
   result=run('check-plan',core,packet,'--core');self.assertEqual(result.returncode,0,result.stderr[-2500:])
   stale=copy.deepcopy(row['steps']);stale[1]['package']['input_core_sha256']=context['source']
   packet=d/'stale-scoped-composition.json';packet.write_bytes(canonical(dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=context['source'],steps=stale)))
   result=run('check-plan',core,packet,'--core');self.assertNotEqual(result.returncode,0)

if __name__=='__main__':unittest.main()
