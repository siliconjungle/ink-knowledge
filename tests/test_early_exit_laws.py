"""A loop shortcut needs both stopping premises and the zero-count branch."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path

class EarlyExitLaws(unittest.TestCase):
 def test_first_step_shortcut_rejects_missing_premises_and_wrong_boundaries(self):
  root=Path(__file__).resolve().parents[2]
  compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source=(root/'knowledge/libraries/early-exit-laws.ink').read_text()
  evidence=root/'knowledge/libraries/proofs/early-exit/source-evidence.json'
  cases=[('valid',source,True),
   ('already-stopped',source.replace(' requires running: stop(state)==false;\n',''),False),
   ('still-running',source.replace(' requires finished: stop(step(0,state))==true;\n',''),False),
   ('wrong-zero',source.replace('choose(count==0,state,step(0,state))','choose(count==1,state,step(0,state))'),False),
   ('wrong-index',source.replace('choose(count==0,state,step(0,state))','choose(count==0,state,step(1,state))'),False)]
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary)
   for name,text,valid in cases:
    path=d/(name+'.ink');path.write_text(text)
    r=subprocess.run([compiler,'emit-laws',path,'--proofs',evidence,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=120)
    self.assertEqual(r.returncode==0,valid,name+': '+r.stderr[-2000:])
    if valid:self.assertEqual(set(json.loads(r.stdout)['names']),{'single_step'})

if __name__=='__main__':unittest.main()
