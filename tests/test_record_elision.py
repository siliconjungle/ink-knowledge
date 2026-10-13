import json,tempfile,unittest
from pathlib import Path
from producers.record_elision import produce,candidates
from producers.physical_capabilities import invoke,write
from producers.workspace import compiler_path
from ink_knowledge.recipes import load,execute

class RecordElision(unittest.TestCase):
 def test_recipe_authors_replayed_composable_layouts_and_declines_unsupported(self):
  compiler=compiler_path('target/debug/ink')
  with tempfile.TemporaryDirectory(prefix='ink-record-test-')as temp:
   root=Path(temp);source=root/'source.ink';source.write_text('module codecs;record Word{value:u32,} record Text{value:String,} record Pair{first:u32,second:u32,} fn word(x:Word)->Word{return x;}')
   core=root/'source.json';invoke(compiler,'emit-core',source,'-o',core);image=json.loads(core.read_bytes())
   plan=produce(source,compiler,root/'proofs',['Word','Text']);self.assertEqual([l['record']for l in plan['record_elisions']],['Text','Word'])
   registry,_=load();recipe=next(r for r in registry['recipes']if r['id']=='private-record-elision')
   context=dict(core=image,compiler=str(compiler),emit_target='javascript',physical=plan)
   proposals=list(execute(recipe,context));self.assertEqual(sum(r['status']=='proposal'for r in proposals),3)
   for row in proposals:
    if row['status']!='proposal':continue
    package=row['step']['package'];self.assertEqual(package['input_core_sha256'],plan['input_core_sha256']);self.assertEqual(package['buffers'],plan['buffers']);path=write(root/'candidate.json',package);invoke(compiler,'check-physical-plan',core,path,'--core')
   self.assertEqual(list(candidates(dict(context,emit_target='rust')))[0]['status'],'declined')
   with self.assertRaisesRegex(ValueError,'exactly one field'):produce(source,compiler,root/'bad',['Pair'])
if __name__=='__main__':unittest.main()
