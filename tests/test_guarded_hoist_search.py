"""Default search ranks ordinary checked guarded hoists across callback forms."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store

SOURCE='''module guarded_search;
pub fn folded(xs:List<u32>,ys:List<u32>)->u32{return foldl(xs,0,fn(x)=>fn(a)=>a+x*foldl(ys,0,fn(y)=>fn(b)=>b+y*y));}
pub fn mapped(xs:List<u32>,ys:List<u32>)->List<u32>{return xs.map(fn(x)=>x+foldl(ys,0,fn(y)=>fn(a)=>a+y*y));}
pub fn filtered(xs:List<u32>,ys:List<u32>)->List<u32>{return xs.filter(fn(x)=>x>foldr(ys,0,fn(y)=>fn(a)=>a+y*y));}
'''
class GuardedHoistSearch(unittest.TestCase):
 def test_default_prices_discover_and_replay_all_three_callback_forms(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);source=d/'source.ink';source.write_text(SOURCE);store=Store.publish(d/'knowledge',[])
   def run(*args):
    r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=180)
    self.assertEqual(r.returncode,0,r.stderr[-3000:]);return r
   core=d/'core.json';run(compiler,'emit-core',source,'-o',core)
   result=run(os.environ.get('PYTHON','python3'),'-m','ink_planner.semantic_search','--compiler',compiler,'--core',core,'--snapshot',store.data/'snapshot.json','--knowledge-root',store.root,'--budget','32','--rounds','4','--time-seconds','30','-o',d/'selected.json')
   report=json.loads(result.stdout);packet=json.loads((d/'selected.json').read_text())
   self.assertLess(report['selected_cost'],report['initial_cost'])
   self.assertEqual({a['function']for a in packet['applications']},{'folded','mapped','filtered'})
   run(compiler,'check-selection',core,d/'selected.json')
   # Retargeting a good law is not authorized by a favorable structural price.
   packet['applications'][0]['function']='missing'
   (d/'forged.json').write_text(json.dumps(packet))
   rejected=subprocess.run([str(compiler),'check-selection',str(core),str(d/'forged.json')],capture_output=True,text=True)
   self.assertNotEqual(rejected.returncode,0)
if __name__=='__main__':unittest.main()
