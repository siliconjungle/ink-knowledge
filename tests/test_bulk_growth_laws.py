import json,os,subprocess,tempfile,unittest
from pathlib import Path
class BulkGrowthLaws(unittest.TestCase):
 def test_decoded_append_fill_and_false_empty_growth(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));source=(root/'knowledge/libraries/bulk-growth-laws.ink').read_text()
  variants=[('valid',source,True),('missing-fill',source.replace('==data.freeze().concat(buffer_fill(count,value).freeze())','==data.freeze()'),False),('nonzero-growth',source.replace('buffer_fill(0,value)','buffer_fill(1,value)'),False)]
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp)
   for label,text,ok in variants:
    p=d/(label+'.ink');p.write_text(text);r=subprocess.run([compiler,'emit-laws',p,'-o',d/(label+'.json')],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode==0,ok,r.stderr[-1000:])
if __name__=='__main__':unittest.main()
