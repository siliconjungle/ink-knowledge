"""General field helper discovery, exact source equality and forged-proof rejection."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.recipes import execute,load
from ink_knowledge.proposal_views import ProposalViews
from producers.frame_projection import candidates
from producers.semantic_laws import word

SOURCE='''module frames;
record Frame{data:Buffer<u32>,fallback:u32,tag:u64,padding:List<u32>,}
fn changed(f:Frame,index:u32)->Frame{if index==0{return f;}let data=f.data.set(index-1,f.fallback);return Frame{..f,data:data};}
fn caller(xs:List<u32>,index:u32)->List<u32>{let frame=Frame{data:buffer(xs),fallback:99,tag:7,padding:[1,2,3]};return changed(frame,index).data.freeze();}
fn computed(xs:List<u32>,index:u32)->List<u32>{return changed(Frame{data:buffer(xs),fallback:99,tag:7,padding:[1]},index).data.freeze();}
fn coupled(f:Frame)->Frame{return Frame{..f,data:f.data.push(f.fallback),tag:f.tag+1};}
fn captured(f:Frame)->Frame{let data=f.data.map(fn(x)=>x+1);return Frame{..f,data:data};}
fn shadowed(f:Frame)->Frame{let f=Frame{..f,tag:8};return Frame{..f,data:f.data.push(3)};}
record Two{first:Buffer<u32>,second:Buffer<u32>,}
fn other_owner(f:Two)->Two{return Two{..f,first:f.first.push(f.second.len())};}
'''

class FrameProjection(unittest.TestCase):
 def test_checked_helper_and_owner_boundaries(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);source=d/'source.ink';source.write_text(SOURCE)
   def run(*args,success=True):
    r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=180);self.assertEqual(r.returncode==0,success,r.stderr[-3000:]);return r
   corefile=d/'core.json';run(compiler,'emit-core',source,'-o',corefile);core=json.loads(corefile.read_text());sid=json.loads(run(compiler,'check-core',corefile).stdout)['core_sha256']
   self.assertEqual([r['original']['name']for r in candidates(core)],['changed']);self.assertEqual(candidates(core,0),[])
   store=Store.publish(d/'knowledge',[]);registry,_=load(store=store);recipe=next(r for r in registry['recipes']if r['id']=='frame-projection')
   rows=list(execute(recipe,dict(core=core,source=sid,compiler=str(compiler.resolve()),knowledge_root=str(store.root),knowledge_snapshot=store.snapshot_id,check_timeout=180)))
   self.assertEqual(len(rows),1,rows);self.assertEqual(rows[0]['status'],'proposal',rows)
   package=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=sid,steps=rows[0]['steps']);plan=d/'plan.json';plan.write_bytes(canonical(package))
   run(compiler,'check-plan',corefile,plan,'--core','--target','javascript');run(compiler,'emit-plan',corefile,plan,'--core','--target','javascript','-o',d/'selected.mjs');run(compiler,'build',corefile,'--core','--target','javascript','-o',d/'baseline.mjs')
   names={a['function']for a in package['steps'][1]['package']['applications']};self.assertIn('caller',names);self.assertNotIn('computed',names)
   script=d/'verify.mjs';script.write_text("""import assert from 'node:assert/strict';import {functions as a} from './selected.mjs';import {functions as b} from './baseline.mjs';
for(const xs of [[],[1],[0,0xffffffff,3]])for(const index of [0,1,2,0xffffffff]){
 assert.deepEqual(a.caller(xs,index),b.caller(xs,index));assert.deepEqual(a.computed(xs,index),b.computed(xs,index));
}console.log('checked field helper preserves clipped edits');""");run('node',script)
   # Change the conclusion, rehash both object and package metadata, and keep
   # the original proof. Discovery must never make this false equality legal.
   bad=copy.deepcopy(package);packet=bad['steps'][1]['package'];view=packet['knowledge'];old=next(iter(view['roots']));obj=copy.deepcopy(view['objects'][old]);obj['payload']['to']['node']['Op'][1][0]['node']['Op'][1][-1]=word('U32',123)
   forged=semantic_entry(dict(schema=1,semantics=obj['semantics'],dependencies=obj['dependencies'],**obj['payload']));fid=identity(forged)
   packet['knowledge']=ProposalViews(store,{fid:forged},d/'forged').bundle([fid])
   for app in packet['applications']:app['law']=fid
   wrong=d/'wrong.json';wrong.write_bytes(canonical(bad));run(compiler,'check-plan',corefile,wrong,'--core','--target','javascript',success=False)
if __name__=='__main__':unittest.main()
