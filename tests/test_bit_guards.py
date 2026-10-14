"""Planner-discovered scalar guards bind real sites and replay every RUP hint."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_knowledge.recipes import execute,load
SOURCE='''module guard_examples;
record Row{value:u32,}
fn masked(value:u64)->u64{return choose((value&255)>255,99,value&255);}
fn captured(xs:List<Row>)->List<u32>{return xs.map(fn(r)=>choose((r.value&15)<=15,r.value&15,99));}
fn unknown(value:u64)->u64{return choose(value<255,1,2);}
fn signed(value:i32)->i32{return choose(value<0,1,2);}
'''
class BitGuards(unittest.TestCase):
 def test_recipe_replays_nested_binders_and_rejects_forged_hints(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);source=d/'source.ink';source.write_text(SOURCE)
   def run(*args,success=True):
    r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode==0,success,r.stderr[-3000:]);return r
   corefile=d/'core.json';run(compiler,'emit-core',source,'-o',corefile);core=json.loads(corefile.read_text());sid=json.loads(run(compiler,'check-core',corefile).stdout)['core_sha256']
   store=Store.publish(d/'knowledge',[]);registry,_=load(store=store);recipe=next(r for r in registry['recipes']if r['id']=='bit-guards')
   rows=list(execute(recipe,dict(core=core,source=sid,compiler=str(compiler.resolve()),knowledge_root=str(store.root),knowledge_snapshot=store.snapshot_id,check_timeout=180)))
   proposals=[r for r in rows if r['status']=='proposal'];self.assertEqual(len(proposals),2,rows)
   apps=[a for r in proposals for a in r['steps'][0]['package']['applications']];self.assertEqual({a['function']for a in apps},{'masked','captured'})
   for r in proposals:
    packet=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=sid,steps=r['steps']);plan=d/'plan.json';plan.write_bytes(canonical(packet))
    run(compiler,'check-plan',corefile,plan,'--core','--target','javascript');run(compiler,'emit-plan',corefile,plan,'--core','--target','javascript','-o',d/'selected.mjs')
    run(compiler,'build',corefile,'--core','--target','javascript','-o',d/'baseline.mjs')
    script=d/'verify.mjs';script.write_text("""import assert from 'node:assert/strict';import{functions as a}from'./selected.mjs';import{functions as b}from'./baseline.mjs';
for(const x of [0n,255n,256n,0xffffffffffffffffn])assert.equal(a.masked(x),b.masked(x));
for(const xs of [[],[{value:0},{value:15},{value:16},{value:0xffffffff}]])assert.deepEqual(a.captured(xs),b.captured(xs));
""");run('node',script)
   bad=copy.deepcopy(proposals[0]['steps'][0]['package']);view=bad['knowledge'];old=view['roots'][0];obj=view['objects'][old]
   obj['payload']['proof']['BitVector']['certificate']['steps'][-1]['hints']=[]
   forged=semantic_entry(dict(schema=1,semantics=obj['semantics'],dependencies=obj['dependencies'],**obj['payload']));fid=identity(forged);bad['knowledge']=ProposalViews(store,{fid:forged},d/'forged').bundle([fid])
   for app in bad['applications']:app['law']=fid
   packet=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=sid,steps=[dict(kind='rewrite',package=bad)]);plan=d/'bad.json';plan.write_bytes(canonical(packet));run(compiler,'check-plan',corefile,plan,'--core','--target','javascript',success=False)
if __name__=='__main__':unittest.main()
