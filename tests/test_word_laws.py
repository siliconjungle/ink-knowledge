"""Installed certificate data reaches ordinary admission, without a solver."""
import gzip,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,semantic_entry,identity
from producers.word_laws import specialize

class WordLaws(unittest.TestCase):
 def test_installed_certificates_replay_and_match_renamed_source_sites(self):
  root=Path(__file__).resolve().parents[2]
  compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
  rows=json.loads(gzip.decompress((Path(__file__).resolve().parents[1]/'producers/data/source-word-laws.json.gz').read_bytes()))
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);source=d/'source.ink';core=d/'core.json';subject=d/'subject.json'
   source.write_text('module independent;fn alphabetic(code:u32)->Bool{return (code>=65 && code<=90)||(code>=97 && code<=122);}fn unrelated(x:u32)->u32{return x*3;}')
   def run(*args):
    p=subprocess.run([str(x)for x in [compiler,*args]],capture_output=True,text=True)
    self.assertEqual(p.returncode,0,p.stderr);return p
   run('emit-core',source,'-o',core);run('emit-semantic',core,'--core','-o',subject)
   objects=[semantic_entry(r['law'])for r in rows]
   st=Store.publish(d/'knowledge',objects);view=d/'view.json';view.write_text(json.dumps(st.bundle([identity(x)for x in objects])))
   run('knowledge-check',core,view)
   proposals=dict(specialize(json.loads(subject.read_text()),json.loads(core.read_text())))
   self.assertIn('word_case_ranges',proposals)
   self.assertEqual(proposals['word_case_ranges'],next(r['law']for r in rows if r['name']=='case_ranges'))
   self.assertEqual(specialize({'functions':{}},{}),[])
