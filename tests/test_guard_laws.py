"""Dominating guards must be identical, and choose remains ordered and lazy."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path

class GuardLaws(unittest.TestCase):
 def test_identical_guards_and_negative_mismatches(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source=(root/'knowledge/libraries/guard-laws.ink').read_text()
  variants=[('valid',source,True),('negated-inner',source.replace('choose(guard,first,second)','choose(!guard,first,second)'),False),('swapped-inner',source.replace('choose(guard,second,third)','choose(guard,third,second)'),False)]
  with tempfile.TemporaryDirectory()as td:
   d=Path(td)
   for name,text,accepted in variants:
    path=d/(name+'.ink');path.write_text(text)
    result=subprocess.run([compiler,'emit-laws',path,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=180)
    self.assertEqual(result.returncode==0,accepted,name+' '+result.stderr[-1500:])
    if accepted:self.assertEqual(set(json.loads(result.stdout)['names']),{'true_guard','false_guard'})
if __name__=='__main__':unittest.main()
