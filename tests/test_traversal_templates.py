import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.law_templates import generate,substitute_types
from producers.traversal_templates import templates
from producers.pipeline_templates import templates as pipelines
from producers.semantic_laws import value,var,law
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))

class TraversalTemplates(unittest.TestCase):
 def test_universal_instances_replay_and_false_results_fail(self):
  with tempfile.TemporaryDirectory()as directory:
   d=Path(directory);core=d/'core.json';source=ROOT/'bench/discovery-reuse/traversals.ink'
   r=subprocess.run([str(COMPILER),'emit-core',str(source),'-o',str(core)],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
   objects=[semantic_entry(substitute_types(row['object']['payload']['law'],{'A':a,'S':s}))for a,s in [('U32','U64'),('String','Bool'),({'List':'U32'},'F32')]for row in templates()]
   st=Store.publish(d/'db',objects);view=d/'view.json';view.write_bytes(canonical(st.bundle(list(st.members()))))
   r=subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
   bad=copy.deepcopy(objects[0]);bad['payload']['to']=bad['payload']['from']['node']['Op'][1][0]
   st=Store.publish(d/'false',[bad]);view.write_bytes(canonical(st.bundle(list(st.members()))))
   r=subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True);self.assertNotEqual(r.returncode,0);self.assertNotIn('hash mismatch',r.stderr)

 def test_repeated_sites_reuse_concrete_instances_and_exact_adapters(self):
  with tempfile.TemporaryDirectory()as directory:
   d=Path(directory);source=d/'source.ink';source.write_text('module Reuse;pub fn f(xs:List<u32>)->u32{return foldr(xs,19,fn(x)=>fn(acc)=>choose(x>3,x*17,acc));}')
   for args in [('emit-core',source,'-o',d/'core.json'),('emit-semantic',d/'core.json','--core','-o',d/'subject.json')]:
    r=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
   subject=json.loads((d/'subject.json').read_bytes());core=json.loads((d/'core.json').read_bytes());st=Store.publish(d/'db',[r['object']for r in pipelines()]);st.rebuild()
   expected,_=generate(st,subject,core);body=subject['functions']['f'];subject['functions']={str(n):body for n in range(64)}
   with patch('ink_knowledge.law_templates.semantic_entry',wraps=semantic_entry)as entries:
    actual,receipts=generate(st,subject,core)
   self.assertEqual(actual,expected);self.assertEqual(entries.call_count,len(actual))
   self.assertGreater(sum(r['instantiation_cache_hits']for r in receipts),0)
   self.assertGreater(sum(r['adapter_cache_hits']for r in receipts),0)

 def test_cached_dependencies_cannot_bypass_depth_budget(self):
  from ink_knowledge import entry
  a=value({'Named':'$A'});x=var(a,'x');rows=[];dep=None
  for _ in range(18):
   payload=dict(type_parameters=['A'],law=law({'x':a},x,x),dependencies={}if dep is None else{'$base':dep})
   obj=entry('definition','ink-semantic-law-template-v1',payload,[]if dep is None else[dep]);rows.append(obj);dep=identity(obj)
  with tempfile.TemporaryDirectory()as directory:
   st=Store.publish(directory,rows)
   # Force dependencies to be cached before the deepest parent is visited.
   with patch('ink_knowledge.template_index.candidates',return_value=[identity(o)for o in rows]):
    with self.assertRaisesRegex(ValueError,'dependency depth'):generate(st,{'functions':{'f':var(value('U32'),'actual')}},{})
