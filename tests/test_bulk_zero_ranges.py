import json,os,subprocess,tempfile,unittest
from pathlib import Path
class BulkZeroRanges(unittest.TestCase):
 def test_zero_work_and_false_nonzero_mutations(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));source=(root/'knowledge/libraries/bulk-range-laws.ink').read_text()
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp)
   for label,text,ok in [('valid',source,True),('nonzero-copy',source.replace('copy_within(source,destination,0)','copy_within(source,destination,1)'),False),('nonzero-fill',source.replace('fill_range(start,0,value)','fill_range(start,1,value)'),False)]:
    p=d/(label+'.ink');p.write_text(text);r=subprocess.run([compiler,'emit-laws',p,'-o',d/(label+'.json')],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode==0,ok,r.stderr[-1000:])
if __name__=='__main__':unittest.main()
