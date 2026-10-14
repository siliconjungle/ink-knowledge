"""Scalar codec proof replay binds every bit of the claimed source equations."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path

class WordRadixLaws(unittest.TestCase):
 def test_certificates_replay_and_reject_missing_bits_or_changed_delta(self):
  root=Path(__file__).resolve().parents[2]
  compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source=root/'knowledge/libraries/word-radix-laws.ink'
  evidence=root/'knowledge/libraries/proofs/word-radix/source-evidence.json'
  original=source.read_text()
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary)
   for name,text,valid in [
    ('valid',original,True),
    ('lost-high-bit',original.replace('& 127,63)','& 0,63)'),False),
    ('shifted-octet',original.replace('& 255,24)','& 255,23)'),False),
    ('wrong-delta',original.replace('previous) ^ previous','previous) | previous'),False),
   ]:
    path=d/(name+'.ink');path.write_text(text)
    result=subprocess.run([compiler,'emit-laws',path,'--proofs',evidence,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=120)
    self.assertEqual(result.returncode==0,valid,name+': '+result.stderr[-2000:])
    if valid:self.assertEqual(len(json.loads(result.stdout)['names']),4)
   swapped=json.loads(evidence.read_text());swapped['radix7_roundtrip']=swapped['octet_roundtrip']
   bad=d/'swapped.json';bad.write_text(json.dumps(swapped))
   result=subprocess.run([compiler,'emit-laws',source,'--proofs',bad,'-o',d/'swapped-output.json'],capture_output=True,text=True,timeout=120)
   self.assertNotEqual(result.returncode,0,result.stderr)

if __name__=='__main__':unittest.main()
