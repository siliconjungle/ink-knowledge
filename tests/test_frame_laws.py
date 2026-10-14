"""Frame traversal laws require concrete preservation of the observed value."""
import json,os
from pathlib import Path
import subprocess,tempfile,unittest

class FrameLaws(unittest.TestCase):
 def test_preservation_and_negative_instances(self):
  root=Path(__file__).resolve().parents[2]
  compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  original=(root/'knowledge/libraries/frame-laws.ink').read_text()
  variants=[('valid',original,True),
    ('missing-premise',original.replace(' assume preserved(item:A,current:S): observe(step(item,current))==observe(current);',''),False),
    ('mutated-data',original.replace('data:c.data','data:[]'),False)]
  with tempfile.TemporaryDirectory() as td:
   d=Path(td)
   for name,source,accepted in variants:
    src=d/(name+'.ink');src.write_text(source)
    result=subprocess.run([compiler,'emit-laws',src,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=180)
    self.assertEqual(result.returncode==0,accepted,name+' '+result.stderr[-1000:])
    if accepted:self.assertEqual(set(json.loads(result.stdout)['names']),{'fold_frame','cursor_data'})
if __name__=='__main__':unittest.main()
