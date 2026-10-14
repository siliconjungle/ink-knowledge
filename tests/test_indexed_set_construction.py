import json,os,subprocess,tempfile,unittest
from pathlib import Path
from producers.set_contracts import derive as prefix
from producers.indexed_set_construction import derive

ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
LIBRARIES=ROOT/'knowledge/libraries'

class IndexedConstruction(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.temp=tempfile.TemporaryDirectory();cls.d=Path(cls.temp.name);cls.framework=cls.d/'framework';cls.framework.mkdir()
  for stem,file in [('storage','storage-observations.ink'),('local','local-relations.ink'),('general','general-laws.ink'),('filter','sequence-filter-laws.ink')]:
   r=subprocess.run([str(COMPILER),'emit-laws',str(LIBRARIES/file),'-o',str(cls.framework/(stem+'-laws.json'))],check=True,capture_output=True,text=True)
   (cls.framework/(stem+'-laws.log')).write_text(r.stdout)
  (cls.d/'empty.ink').write_text('module Empty;fn same(x:u32)->u32{return x;}')
  cls.empty=cls.d/'empty.core.json';subprocess.run([str(COMPILER),'emit-core',str(cls.d/'empty.ink'),'-o',str(cls.empty)],check=True,capture_output=True,text=True)
  cls.source='''module Construction;
import %s as sets;
record Build{seen:Map<u32,Bool>,out:Buffer<u32>,}
fn baseline(xs:List<u32>)->List<u32>{return sets.elements<u32>(sets.set<u32>(xs));}
fn valid(xs:List<u32>)->Bool{return sets.distinct<u32>(xs);}
fn step(item:u32,r:Build)->Build{
 let present:Bool=r.seen.contains(item);let seen:Map<u32,Bool>=r.seen.set(item,true);let out:Buffer<u32>=r.out;
 if present{return Build{seen:seen,out:out};}return Build{seen:seen,out:out.push(item)};
}
spec fn make(xs:List<u32>)->List<u32> ensures valid(result);
implementation constructed for make{let built:Build=foldl(xs,Build{seen:Map.empty(),out:Buffer.empty()},fn(item)=>fn(r)=>step(item,r));return built.out.freeze();}
'''%json.dumps(str(LIBRARIES/'collections.ink'))
 @classmethod
 def tearDownClass(cls):cls.temp.cleanup()
 def author(self,source,stem):
  d=self.d/stem;d.mkdir();p=d/'source.ink';p.write_text(source);goals=d/'goals.json'
  subprocess.run([str(COMPILER),'emit-contract-obligations',str(p),'-o',str(goals)],check=True,capture_output=True,text=True)
  context=json.loads(goals.read_text())['definition_context']
  component=prefix(COMPILER,context,d/'prefix',self.framework,self.empty)
  return derive(COMPILER,context,component,d,self.framework,self.empty)
 def test_map_buffer_relation_proves_complete_construction(self):
  result=self.author(self.source,'good');self.assertIn(result['construction'],result['objects'])
 def test_duplicate_push_cannot_preserve_the_set_interface(self):
  with self.assertRaisesRegex(ValueError,'indexed_step_preserves: error:.*semantic normal forms differ'):
   self.author(self.source.replace('out:out.push(item)','out:out.push(item).push(item)'),'duplicate')

if __name__=='__main__':unittest.main()
