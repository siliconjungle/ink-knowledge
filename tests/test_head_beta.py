"""Search through lexical bindings; the original endpoints still require proof."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge.head_beta import reduce,contexts
from ink_knowledge.template_matching import TemplateSites
from ink_knowledge.higher_patterns import adapter
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.law_templates import from_general,generate
from producers.semantic_laws import value,arrow,var,bound,lam,op
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))

class HeadBeta(unittest.TestCase):
 def test_capture_avoidance_and_shadowing_preserve_outer_indices(self):
  u=value('U32')
  # (fn(x)=>fn(y)=>x+y)(outer) must retain outer beneath y.
  term=op(arrow(u,u),'apply',lam(u,lam(u,op(u,'binary:+',bound(u,1),bound(u,0)))),bound(u,0))
  original=copy.deepcopy(term)
  self.assertEqual(reduce(term),lam(u,op(u,'binary:+',bound(u,1),bound(u,0))))
  self.assertEqual(term,original)
  concrete=op(u,'apply',lam(u,op(u,'apply',lam(u,bound(u,0)),var(u,'inner'))),var(u,'outer'))
  self.assertEqual(reduce(concrete),var(u,'inner'))
  # A non-leading expression stays literal: this is not full normalisation.
  outer=op(u,'binary:+',concrete,var(u,'x'));self.assertIs(reduce(outer),outer)
 def test_bounds_preserve_original_discovery_and_open_adapters_reject(self):
  u=value('U32');target=op(u,'apply',lam(u,op(u,'call:f',bound(u,0))),var(u,'arg'))
  with self.assertRaisesRegex(ValueError,'budget'):reduce(target,limit=1)
  from ink_planner.semantic_search import positions
  count=len(list(positions(target)))
  sites=TemplateSites({'functions':{'run':target}},node_limit=count)
  self.assertEqual(len(sites.sites),count);self.assertEqual(sites.head_reductions,0)
  self.assertGreater(sites.head_reduction_declines,0)
  self.assertEqual(sites.sites[0],('run',(),target))
  limited=TemplateSites({'functions':{'run':target}},node_limit=count+1)
  self.assertEqual(limited.sites[:count],sites.sites)
  self.assertLessEqual(len(limited.sites),count+1)
  self.assertGreater(limited.head_reduction_declines,0)
  # Context lifting must not turn a callback-local value into a free value.
  callback=lam(u,op(u,'call:f',bound(u,0)))
  self.assertEqual(list(contexts(callback)),[((),callback)])
  with self.assertRaisesRegex(ValueError,'budget'):list(contexts(target,limit=1))
  law=dict(params={'x':u},conditions=[],**{'from':op(u,'call:f',var(u,'x')),'to':var(u,'x')})
  opened=op(u,'apply',lam(u,op(u,'call:f',bound(u,0))),bound(u,0))
  self.assertIsNone(adapter('0'*64,law,opened))
  conditional=dict(law,conditions=[{'from':var(u,'x'),'to':var(u,'x')}])
  conditioned=adapter('0'*64,conditional,target)
  self.assertEqual(len(conditioned['conditions']),1)
  self.assertIn("'Hypothesis': 0",repr(conditioned['proof']))
  repeated=op(u,'apply',lam(u,op(u,'binary:+',op(u,'call:f',bound(u,0)),op(u,'call:f',bound(u,0)))),var(u,'arg'))
  matches=list(TemplateSites({'functions':{'run':repeated}}).matches(law['from'],law['params'],[]))
  self.assertEqual(len([row for row in matches if row[1]==()]),1)
 def test_conditional_adapter_requires_explicit_true_premises_after_head_reduction(self):
  from producers.semantic_laws import law
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);source=d/'source.ink'
   source.write_text('module conditional_adapter;fn valid(x:u32)->u32{let alias=x;return x+alias;}fn distinct(x:u32,y:u32)->u32{let alias=y;return x+alias;}')
   def invoke(*args):return subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True,timeout=120)
   result=invoke('emit-core',source,'-o',d/'core.json');self.assertEqual(result.returncode,0,result.stderr)
   result=invoke('emit-semantic',d/'core.json','--core','-o',d/'subject.json');self.assertEqual(result.returncode,0,result.stderr)
   subject=json.loads((d/'subject.json').read_text());u=value('U32');a,b=var(u,'a'),var(u,'b')
   original=semantic_entry(law({'a':u,'b':u},op(u,'binary:+',a,b),op(u,'binary:+',a,a),
    {'Congruence':['Normalize',{'Sym':{'Hypothesis':0}}]},conditions=[{'from':a,'to':b}]))
   ident=identity(original);store=Store.publish(d/'knowledge',[original])
   for name in ['valid','distinct']:
    authored=adapter(ident,original['payload'],subject['functions'][name]);self.assertIsNotNone(authored)
    obj=semantic_entry(dict(schema=1,**authored));root=identity(obj);store=store.extend([obj])
    packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],
     knowledge=store.bundle([root]),applications=[dict(function=name,path=[],law=root,
      arguments={n:var(s,n)for n,s in authored['params'].items()},premises=['Normalize'])])
    path=d/(name+'.json');path.write_bytes(canonical(packet));result=invoke('check-selection',d/'core.json',path)
    self.assertEqual(result.returncode==0,name=='valid',result.stderr)
    if name=='distinct':self.assertIn('premise 0',result.stderr)
    else:
     packet['applications'][0]['premises']=[];path.write_bytes(canonical(packet));result=invoke('check-selection',d/'core.json',path)
     self.assertNotEqual(result.returncode,0);self.assertIn('arity',result.stderr)

 def test_generic_fold_template_replays_original_bound_source_and_rejects_forgery(self):
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);source=d/'source.ink';laws=d/'laws.ink'
   source.write_text('module bound; record Totals { sum:u32, count:u32, } pub fn projected(xs:List<u32>,bias:u32)->u32{let seed=Totals {sum:bias,count:0};return foldl(xs,seed,fn(x,s)=>Totals {sum:s.sum+x,count:s.count+1}).sum+bias;} pub fn words(xs:List<u32>,bias:u32)->u32{let seed=bias+7;return foldl(xs,seed,fn(x,s)=>s*3+x);} pub fn floats(xs:List<f32>,bias:f32)->f32{let seed=bias;return foldr(xs,seed,fn(x,s)=>(s+x)*x);}')
   laws.write_text('module laws; law left<A,S>(xs:List<A>,initial:S,step:fn(A,S)->S){foldl(xs,initial,step)==choose(xs==[],initial,foldl(xs,initial,step));proof by induction xs {nil=>normalize;cons(head,tail)=>normalize;};} law right<A,S>(xs:List<A>,initial:S,step:fn(A,S)->S){foldr(xs,initial,step)==choose(xs==[],initial,foldr(xs,initial,step));proof by induction xs {nil=>normalize;cons(head,tail)=>normalize;};}')
   def invoke(*args):
    r=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr);return r
   receipt=json.loads(invoke('emit-laws',laws,'-o',d/'laws.json').stdout)
   bundle=json.loads((d/'laws.json').read_text());store=Store.publish(d/'knowledge',bundle['objects'].values())
   store=store.extend([from_general(store,i)for i in receipt['names'].values()]);store.refresh_index()
   core_id=json.loads(invoke('emit-core',source,'-o',d/'core.json').stdout)['core_sha256']
   invoke('emit-semantic',d/'core.json','--core','-o',d/'subject.json')
   core=json.loads((d/'core.json').read_text());subject=json.loads((d/'subject.json').read_text())
   objects,_=generate(store,subject,core);store=store.extend(objects.values());applications=[];adapters={}
   for name,body in subject['functions'].items():
    for ident,obj in objects.items():
     if obj['payload']['from']==body:
      adapters[name]=(ident,obj)
      applications.append(dict(function=name,path=[],law=ident,arguments={n:dict(sort=s,node={'Free':n})for n,s in obj['payload']['params'].items()},premises=[]))
   self.assertEqual(set(adapters),{'words','floats','projected'})
   self.assertIn('Congruence',adapters['projected'][1]['payload']['proof']['Trans']['right'])
   package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=core_id,knowledge=store.bundle([a['law']for a in applications]),applications=applications)
   plan=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=core_id,steps=[dict(kind='rewrite',package=package)])
   (d/'plan.json').write_bytes(canonical(plan));invoke('check-plan',source,d/'plan.json','--target','javascript')
   invoke('emit-plan',source,d/'plan.json','--target','javascript','-o',d/'selected.mjs')
   invoke('build',source,'--target','javascript','-o',d/'baseline.mjs')
   driver=d/'check.mjs';driver.write_text("import assert from 'node:assert/strict';import * as a from './baseline.mjs';import * as b from './selected.mjs';for(const xs of [[],[0],[1,2,4294967295]])for(const seed of [0,7,4294967295]){assert.deepStrictEqual(a.call('words',[xs,seed]),b.call('words',[xs,seed]));assert.deepStrictEqual(a.call('projected',[xs,seed]),b.call('projected',[xs,seed]));}for(const xs of [[],[1e20,-1e20,3],[-0,Infinity,-Infinity,NaN]])for(const seed of [-0,0,1e20])assert.deepStrictEqual(a.functions.floats(xs,seed),b.functions.floats(xs,seed));")
   result=subprocess.run(['node',str(driver)],capture_output=True,text=True);self.assertEqual(result.returncode,0,result.stderr)
   for name in ['words','projected']:
    _,obj=adapters[name];forged=copy.deepcopy(obj);forged['payload']['to']=dict(sort=value('U32'),node={'Word':0})
    forged=semantic_entry(dict(schema=1,semantics=forged['semantics'],dependencies=forged['dependencies'],**forged['payload']))
    store=store.extend([forged]);(d/'forged.json').write_bytes(canonical(store.bundle([identity(forged)])))
    result=subprocess.run([str(COMPILER),'knowledge-check',str(d/'core.json'),str(d/'forged.json')],capture_output=True,text=True)
    self.assertNotEqual(result.returncode,0);self.assertNotIn('hash mismatch',result.stderr)

if __name__=='__main__':unittest.main()
