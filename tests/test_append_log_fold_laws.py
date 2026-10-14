import os,subprocess,tempfile,unittest
from pathlib import Path
class AppendLogFoldLaws(unittest.TestCase):
 def test_ordered_incremental_replay_and_false_reordering(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));source=(root/'knowledge/libraries/append-log-fold-laws.ink').read_text()
  variants=[('valid',source,True),('reordered',source.replace('foldl(incoming,foldl(history,initial,step),step)','foldl(history,foldl(incoming,initial,step),step)'),False),('dropped',source.replace('foldl(incoming,foldl(history,initial,step),step)','foldl(incoming,initial,step)'),False)]
  with tempfile.TemporaryDirectory()as temp:
   for label,text,ok in variants:
    path=Path(temp)/(label+'.ink');path.write_text(text);r=subprocess.run([compiler,'emit-laws',path,'-o',Path(temp)/(label+'.json')],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode==0,ok,r.stderr[-2000:])
if __name__=='__main__':unittest.main()
