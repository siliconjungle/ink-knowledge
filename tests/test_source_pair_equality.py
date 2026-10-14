"""Explicit source reductions must replay and must reject changed bodies."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path

class SourcePairEquality(unittest.TestCase):
 def test_renamed_parameters_record_wrappers_and_changed_result(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source='''module pair;
record Left{data:List<u32>,position:u32,}
record Right{data:List<u32>,position:u32,}
fn shared(xs:List<u32>)->List<u32>{return xs.map(fn(x)=>x+1);}
fn left_step(s:Left,yes:Bool)->Left{return choose(yes,Left{data:shared(s.data),position:s.position+1},s);}
fn right_step(t:Right,flag:Bool)->Right{let position=t.position+1;return choose(flag,Right{data:shared(t.data),position:position},t);}
fn first(xs:List<u32>,at:u32,yes:Bool)->List<u32>{return left_step(Left{data:xs,position:at},yes).data;}
fn second(values:List<u32>,position:u32,flag:Bool)->List<u32>{return right_step(Right{data:values,position:position},flag).data;}
'''
  for label,text,accepted in [('same',source,True),('changed',source.replace('data:shared(t.data)','data:[]'),False)]:
   with tempfile.TemporaryDirectory()as temporary:
    d=Path(temporary);src=d/'source.ink';src.write_text(text);core=d/'core.json'
    result=subprocess.run([compiler,'emit-core',src,'-o',core],capture_output=True,text=True,timeout=180);self.assertEqual(result.returncode,0,result.stderr[-2000:])
    command=[os.environ.get('INK_PYTHON','python3'),root/'tools/source_pair_equality.py','--compiler',compiler,'--core',core,'--left','first','--right','second','-o',d/'proofs']
    result=subprocess.run(list(map(str,command)),capture_output=True,text=True,timeout=180)
    self.assertEqual(result.returncode==0,accepted,label+' '+result.stderr[-2500:])
    if accepted:self.assertEqual(json.loads(result.stdout)['status'],'checked')
    else:self.assertFalse((d/'proofs').exists())


 def test_explicit_shared_guard_unfold_skips_opaque_loop(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source='module guarded;fn heavy(xs:List<u32>)->List<u32>{return repeat_until(4294967295,xs,fn(xs)=>false,fn(i,xs)=>xs.map(fn(x)=>x+1));} fn choose_value(xs:List<u32>,yes:Bool)->List<u32>{return choose(yes,xs,heavy(xs));} fn first(xs:List<u32>,yes:Bool)->List<u32>{return choose_value(xs,yes);} fn second(xs:List<u32>,yes:Bool)->List<u32>{return choose(yes,xs,choose_value(xs,yes));}'
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);src=d/'source.ink';src.write_text(source);core=d/'core.json'
   result=subprocess.run([compiler,'emit-core',src,'-o',core],capture_output=True,text=True,timeout=120);self.assertEqual(result.returncode,0,result.stderr)
   result=subprocess.run(list(map(str,[os.environ.get('INK_PYTHON','python3'),root/'tools/source_pair_equality.py','--compiler',compiler,'--core',core,'--left','first','--right','second','--unfold','choose_value','-o',d/'proof'])),capture_output=True,text=True,timeout=120);self.assertEqual(result.returncode,0,result.stderr[-1800:]);self.assertEqual(json.loads(result.stdout)['status'],'checked')

 def test_explicit_guard_is_checked_and_false_branch_rejects(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source='module guard;fn first(xs:List<u32>,yes:Bool)->List<u32>{return choose(yes,xs,[]);}fn second(xs:List<u32>,yes:Bool)->List<u32>{return choose(yes,xs,[]);}'
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp);guard=d/'guard.json';guard.write_text(json.dumps({'sort':{'Value':'Bool'},'node':{'Free':'yes'}}))
   for label,text,ok in [('valid',source,True),('false',source.replace('fn second(xs:List<u32>,yes:Bool)->List<u32>{return choose(yes,xs,[]);}','fn second(xs:List<u32>,yes:Bool)->List<u32>{return choose(yes,[],xs);}'),False)]:
    path=d/(label+'.ink');path.write_text(text);core=d/(label+'.json');r=subprocess.run([compiler,'emit-core',path,'-o',core],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
    r=subprocess.run(list(map(str,[os.environ.get('INK_PYTHON','python3'),root/'tools/source_pair_equality.py','--compiler',compiler,'--core',core,'--left','first','--right','second','--guard',guard,'-o',d/(label+'-proof')])),capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode==0,ok,r.stderr[-1500:])

if __name__=='__main__':unittest.main()
