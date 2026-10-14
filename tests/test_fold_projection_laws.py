import json,os,subprocess,tempfile,unittest
from pathlib import Path
class FoldProjectionLaws(unittest.TestCase):
 def test_projection_needs_step_simulation(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));source=(root/'knowledge/libraries/fold-projection-laws.ink').read_text()
  concrete="""
record State{value:u32,ignored:u32,}
law projected(xs:List<u32>,initial:State){
 foldl(xs,initial,fn(item,s)=>State{value:s.value+item,ignored:s.ignored+1}).value==foldl(xs,initial.value,fn(item,v)=>v+item);
 proof by use fold_projection<u32,State,u32>(xs,initial,fn(s)=>s.value,fn(item,s)=>State{value:s.value+item,ignored:s.ignored+1},fn(item,v)=>v+item) assuming(normalize);
}
"""
  variants=[('valid',source+concrete,True),('false-step',source+concrete.replace('ignored:s.ignored+1}).value','ignored:s.ignored+1}).value').replace('value:s.value+item','value:s.ignored+item'),False),('missing-assumption',source.replace(' assume simulation(item:A,state:S): project(step(item,state))==reduced(item,project(state));',''),False)]
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp)
   for name,text,accepted in variants:
    path=d/(name+'.ink');path.write_text(text);r=subprocess.run([compiler,'emit-laws',path,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode==0,accepted,name+' '+r.stderr[-1000:])
if __name__=='__main__':unittest.main()
