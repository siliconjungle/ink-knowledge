import os,subprocess,tempfile,unittest
from pathlib import Path
class HistoryBufferLaws(unittest.TestCase):
 def test_append_accumulator_and_false_missing_or_reversed_values(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));source=(root/'knowledge/libraries/history-buffer-laws.ink').read_text()
  variants=[('valid',source,True),('dropped',source.replace('current.concat([value])','current'),False),('reversed',source.replace('current.concat([value])','[value].concat(current)'),False)]
  with tempfile.TemporaryDirectory()as temp:
   for label,text,ok in variants:
    path=Path(temp)/(label+'.ink');path.write_text(text);result=subprocess.run([compiler,'emit-laws',path,'-o',Path(temp)/(label+'.json')],capture_output=True,text=True,timeout=120);self.assertEqual(result.returncode==0,ok,result.stderr[-1500:])
if __name__=='__main__':unittest.main()
