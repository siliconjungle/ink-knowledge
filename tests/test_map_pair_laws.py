import json,os,subprocess,tempfile,unittest
from pathlib import Path
class MapPairLaws(unittest.TestCase):
 def test_last_write_lookup_and_reject_false_decodings(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));source=(root/'knowledge/libraries/map-pair-laws.ink').read_text()
  variants=[('valid',source,True),('wrong-key',source.replace('choose(key==entry.key,entry.value,value)','choose(key==entry.key,value,entry.value)'),False),('first-write',source.replace('==foldl(entries,initial.get_or(key,fallback)','==foldr(entries,initial.get_or(key,fallback)'),False)]
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp)
   for name,text,accepted in variants:
    path=d/(name+'.ink');path.write_text(text);r=subprocess.run([compiler,'emit-laws',path,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=120)
    self.assertEqual(r.returncode==0,accepted,name+' '+r.stderr[-1000:])
    if accepted:self.assertEqual(set(json.loads(r.stdout)['names']),{'decode_lookup'})
if __name__=='__main__':unittest.main()
