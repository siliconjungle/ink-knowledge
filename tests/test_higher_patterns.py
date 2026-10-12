import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from ink_knowledge.higher_patterns import match
from ink_knowledge.law_templates import generate
from ink_knowledge.proposal_views import ProposalViews
from producers.pipeline_templates import templates
from producers.semantic_laws import value,arrow,var,bound,lam,op
from ink_planner.semantic_search import match as exact_match
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
class HigherPatterns(unittest.TestCase):
 def test_abstraction_permutation_nesting_and_capture_rejection(self):
  u=value('U32');f=var(arrow(u,arrow(u,u)),'f');params={'f':f['sort']}
  applied=lambda a,b:op(u,'apply',op(arrow(u,u),'apply',f,bound(u,a)),bound(u,b))
  pattern=lam(u,lam(u,applied(1,0)));actual=lam(u,lam(u,op(u,'binary:-',bound(u,0),bound(u,1))))
  args={};self.assertTrue(match(pattern,actual,params,[],{},args))
  self.assertEqual(args['f'],lam(u,lam(u,op(u,'binary:-',bound(u,0),bound(u,1)))))
  single=var(arrow(u,u),'p');pattern=lam(u,lam(u,op(u,'apply',single,bound(u,1))))
  self.assertFalse(match(pattern,actual,{'p':single['sort']},[],{},{}))
  outer=lam(u,lam(u,op(u,'binary:+',bound(u,1),var(u,'capture'))));args={}
  self.assertTrue(match(pattern,outer,{'p':single['sort']},[],{},args))
  self.assertEqual(args['p'],lam(u,op(u,'binary:+',bound(u,0),var(u,'capture'))))
  repeated=lam(u,lam(u,applied(0,0)))
  self.assertFalse(match(repeated,actual,params,[],{},{}))
 def test_exact_adapters_replay_and_rehashed_false_adapters_reject(self):
  with tempfile.TemporaryDirectory()as d:
   d=Path(d);source=d/'source.ink';source.write_text('module Adapter; record Row{key:u32,label:String,} pub fn first(xs:List<Row>,cut:u32)->String{return foldr(xs,"missing",fn(x)=>fn(acc)=>choose(x.key>cut,x.label,acc));} pub fn dependent(xs:List<Row>,cut:u32)->u32{return foldr(xs,0,fn(x)=>fn(acc)=>choose(x.key>cut,x.key+acc,acc));}')
   def invoke(*args):
    r=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr);return r
   core=d/'core.json';sub=d/'subject.json';invoke('emit-core',source,'-o',core);invoke('emit-semantic',core,'--core','-o',sub)
   row=next(r for r in templates()if r['name']=='foldr-first-replacement');st=Store.publish(d/'store',[row['object']]);objects,receipts=generate(st,json.loads(sub.read_text()),json.loads(core.read_text()))
   adapters=[(ident,obj)for ident,obj in objects.items()if obj['payload']['from']==json.loads(sub.read_text())['functions']['first']]
   self.assertEqual(len(adapters),1);ident,obj=adapters[0];args={};self.assertTrue(exact_match(obj['payload']['from'],json.loads(sub.read_text())['functions']['first'],obj['payload']['params'],args))
   package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=json.loads(sub.read_text())['input_core_sha256'],knowledge=ProposalViews(st,objects,d/'views').bundle([ident]),applications=[dict(function='first',path=[],law=ident,arguments=args,premises=[])])
   selection=d/'selection.json';selection.write_bytes(canonical(package));invoke('check-selection',core,selection)
   # Editing a result and rehashing every enclosing object is insufficient.
   forged=copy.deepcopy(obj);forged['payload']['to']['node']['Op'][1][1]=dict(sort=value('String'),node={'Text':'forged'})
   rows=[forged if key==ident else value for key,value in objects.items()];bad=Store.publish(d/'bad',rows);view=d/'bad.json';view.write_bytes(canonical(bad.bundle([identity(forged)])))
   r=subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True);self.assertNotEqual(r.returncode,0);self.assertNotIn('hash mismatch',r.stderr)
