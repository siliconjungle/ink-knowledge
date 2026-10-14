import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,identity,semantic_entry
from ink_knowledge.law_templates import generate
from producers.sequence_search import publish,LIBRARIES,source_applicability

ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))

class SequenceSearch(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.temp=tempfile.TemporaryDirectory();cls.d=Path(cls.temp.name)
  Store.publish(cls.d/'knowledge',[])
  cls.receipt=publish(COMPILER,cls.d/'knowledge');cls.store=Store(cls.d/'knowledge')
 @classmethod
 def tearDownClass(cls):cls.temp.cleanup()
 def core(self,source,stem):
  p=self.d/(stem+'.ink');p.write_text(source);out=self.d/(stem+'.core.json')
  subprocess.run([str(COMPILER),'emit-core',str(p),'-o',str(out)],check=True,capture_output=True,text=True)
  return out
 def check(self,core,bundle):
  view=self.d/'check.json';view.write_text(json.dumps(bundle))
  return subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True)
 def test_template_transports_structural_predicates_across_carriers(self):
  core=self.core('''module Searches;
record Row{name:String,bits:List<f32>,}
fn words(xs:List<u32>,item:u32)->Bool{return foldr(xs,false,fn(x)=>fn(found)=>[x]==[item]||found);}
fn floats(xs:List<f32>,item:f32)->Bool{return foldr(xs,false,fn(x)=>fn(found)=>[x]==[item]||found);}
fn records(xs:List<Row>,item:Row)->Bool{return foldr(xs,false,fn(x)=>fn(found)=>[x]==[item]||found);}
fn total(xs:List<u32>)->u32{return sum(xs);}
''','searches')
  subject=self.d/'subject.json'
  subprocess.run([str(COMPILER),'emit-semantic',str(core),'--core','-o',str(subject)],check=True,capture_output=True,text=True)
  objects,receipt=generate(self.store,json.loads(subject.read_text()),json.loads(core.read_text()))
  self.assertEqual(sum(r['instances'] for r in receipt),3)
  bank=Store.publish(self.d/'instances',objects.values())
  result=self.check(core,bank.bundle(sorted(objects)));self.assertEqual(result.returncode,0,result.stderr)
 def test_fresh_membership_cannot_rescue_a_false_search_proof(self):
  core=self.core('module Empty;fn identity(x:u32)->u32{return x;}','empty')
  ident=self.receipt['names']['sequence-search/foldr_any'];obj=copy.deepcopy(self.store.object(ident))
  obj['payload']['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']={'sort':{'Value':'Bool'},'node':{'Bool':True}}
  bad=semantic_entry(dict(schema=1,semantics=obj['semantics'],dependencies=obj['dependencies'],**obj['payload']));bank=Store.publish(self.d/'false',[bad]);result=self.check(core,bank.bundle([identity(bad)]))
  self.assertNotEqual(result.returncode,0);self.assertIn('condition does not establish goal',result.stderr)
 def test_index_proof_binds_actual_executable_helpers(self):
  ident=self.receipt['names']['sequence-search/indexed_intersection_u32'];bundle=self.store.bundle([ident])
  source=(LIBRARIES/'indexed-sequences.ink').read_text()
  result=source_applicability(COMPILER,self.core(source,'same-index'),bundle,self.d);self.assertEqual(result.returncode,0,result.stderr)
  altered=source.replace('seen.set(item,true)','seen')
  result=source_applicability(COMPILER,self.core(altered,'changed-index'),bundle,self.d);self.assertNotEqual(result.returncode,0);self.assertIn('definition context body differs',result.stderr)

if __name__=='__main__':unittest.main()
