import os,subprocess,tempfile,unittest
from pathlib import Path

class UnchangingReadLaws(unittest.TestCase):
 def test_entire_state_preservation_is_required_for_reuse(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source=(root/'knowledge/libraries/unchanging-read-laws.ink').read_text()
  missing=source.replace(' assume preserved(current:S): recover(read(current))==current;\n','')
  weakened=source.replace('recover(read(current))==current','current==current')
  other=source.replace('state:S,read:','state:S,other:S,read:').replace('==read(state);','==read(other);')
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary)
   for name,text,valid in [('valid',source,True),('missing',missing,False),('weakened',weakened,False),('other-state',other,False)]:
    path=d/(name+'.ink');path.write_text(text);r=subprocess.run([compiler,'emit-laws',path,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=120)
    self.assertEqual(r.returncode==0,valid,name+': '+r.stderr[-2000:])

if __name__=='__main__':unittest.main()
