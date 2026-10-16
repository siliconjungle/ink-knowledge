"""Compact membership transport preserves exact closure and kernel authority."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from producers.semantic_laws import law,value,var,binary,word

class MembershipTransport(unittest.TestCase):
 def test_small_leaves_reduce_repeated_metadata_without_granting_authority(self):
  s=value('U32');x=var(s,'x');support=law({'x':s},binary('+',x,word('U32',0)),x);obj=semantic_entry(support);sid=identity(obj)
  consumer=copy.deepcopy(support);consumer['dependencies']=[sid];consumer['proof']={'Use':dict(law=sid,arguments={'x':x},premises=[])};root=semantic_entry(consumer);rid=identity(root)
  fillers=[semantic_entry(law({'x':s},binary('-',binary('+',x,word('U32',i)),word('U32',i)),x))for i in range(1,97)]
  objects={identity(o):o for o in [root,*fillers]}
  repo=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',repo/'target/debug/ink'))
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);source=Store.publish(d/'source',[obj]);views=ProposalViews(source,objects,d/'transport');compact=views.bundle([rid])
   wide=Store.publish(d/'wide',[obj,*objects.values()],leaf_size=64).bundle([rid])
   self.assertEqual(compact['objects'],wide['objects']);self.assertEqual(set(compact['membership']),{rid,sid})
   self.assertLess(len(canonical(compact)),len(canonical(wide)))
   source_file=d/'source.ink';source_file.write_text('module membership; fn id(x:u32)->u32{return x;}')
   subprocess.run([compiler,'emit-core',source_file,'-o',d/'core.json'],check=True,capture_output=True,text=True,timeout=120)
   def check(view):
    (d/'view.json').write_bytes(canonical(view));return subprocess.run([compiler,'knowledge-check',d/'core.json',d/'view.json'],capture_output=True,text=True,timeout=120)
   self.assertEqual(check(compact).returncode,0);self.assertEqual(check(wide).returncode,0)
   tampered=copy.deepcopy(compact);tampered['membership'][sid]=tampered['membership'][rid]
   self.assertNotEqual(check(tampered).returncode,0)
   false=copy.deepcopy(support);false['to']=binary('+',x,word('U32',1));bad=semantic_entry(false);bid=identity(bad)
   # Authentic rehashed membership is still insufficient for a false equation.
   extra=ProposalViews(source,{bid:bad},d/'false');self.assertNotEqual(check(extra.bundle([bid])).returncode,0)

if __name__=='__main__':unittest.main()
