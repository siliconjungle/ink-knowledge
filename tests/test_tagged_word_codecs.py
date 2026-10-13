import json,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical
from producers.tagged_word_codecs import produce,goals
from producers.bitvector_proofs import certificate
from producers.workspace import compiler_path

class TaggedWords(unittest.TestCase):
 def test_all_widths_replay_and_forged_modes_and_false_equations_fail(self):
  compiler=compiler_path('target/debug/ink')
  with tempfile.TemporaryDirectory(prefix='ink-tag-tests-')as tmp:
   root=Path(tmp);store,names=produce(compiler,root/'knowledge')
   self.assertEqual(len(names),48)
   source=root/'context.ink';core=root/'context.json';source.write_text('module tag_tests; fn identity(x: u64) -> u64 { return x; }')
   subprocess.run([str(compiler),'emit-core',str(source),'-o',str(core)],check=True,capture_output=True)
   objects=[json.loads(p.read_bytes())for p in (store.data/'objects').glob('*.json')]
   self.assertTrue(all(v['payload']['declaration']['Theorem']['proof']['BitVector']['certificate']['encoding']=='shared-v2'for v in objects))
   self.assertLess(max(len(canonical(v))for v in objects),200000)
   for corruption in ['encoding','statement','hint']:
    bad=json.loads(json.dumps(objects[0]));theorem=bad['payload']['declaration']['Theorem'];proof=theorem['proof']['BitVector']
    if corruption=='encoding':proof['certificate']['encoding']='literal-v1'
    elif corruption=='statement':theorem['to']={'U64':123};proof['to']={'U64':123}
    else:proof['certificate']['steps'][-1]['hints']=[]
    forged=Store.publish(root/corruption,[bad]);view=root/(corruption+'.json');view.write_bytes(canonical(forged.bundle(list(forged.members())))+b'\n')
    r=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],capture_output=True,text=True);self.assertNotEqual(r.returncode,0);self.assertNotIn('hash mismatch',r.stderr)
   goal=goals(3)['tag'];goal['to']={'Var':'payload'};path=root/'false.json';cnf=root/'false-cnf.json';path.write_bytes(canonical(goal)+b'\n')
   subprocess.run([str(compiler),'bitvector-obligation',str(path),'-o',str(cnf),'--circuit','shared-v2'],check=True,capture_output=True)
   with self.assertRaisesRegex(ValueError,'counterexample'):certificate(json.loads(cnf.read_bytes()),seconds=5,conflicts=20000)
 def test_widths_are_bounded(self):
  for bits in [0,13,-1]:
   with self.assertRaises(ValueError):goals(bits)
if __name__=='__main__':unittest.main()
