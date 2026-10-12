import copy,json,os,sqlite3,subprocess,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
from ink_knowledge import Store,entry,identity,canonical
from ink_knowledge.template_index import candidates
from ink_knowledge.template_matching import TemplateSites
from ink_knowledge.object_pack import pack
from ink_knowledge.source_algorithms import resolve,propose,publish
from ink_knowledge.selectors import matches,evaluate
from ink_knowledge.recipes import load
from ink_knowledge.family_evidence import page as family_evidence
from producers.planning_recipes import physical
from producers.pipeline_templates import templates
from producers.semantic_laws import value,var,op

ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))

class ComposableKnowledge(unittest.TestCase):
 def test_family_attribution_is_exact_separate_evidence_and_survives_index_rebuild(self):
  with tempfile.TemporaryDirectory()as d:
   a=entry('definition','test-v1',{'body':'family'});st=Store.publish(d,[a]);st.rebuild();pin=st.snapshot_id
   target=dict(hardware='test',driver='none',toolchain='compiler-pinned',backend='javascript',bridge='trusted');workload=dict(shape=[128],distribution='late',concurrency=1,residency='host')
   obs=dict(schema=1,program='b'*64,entries=[identity(a)],plan='c'*64,target=target,workload=workload,metrics=dict(complete_call_ns=['100','110'],peak_bytes=None))
   ident=st.observe(obs);self.assertEqual(family_evidence(st,[identity(a)],target,workload),[obs]);self.assertEqual(st.snapshot_id,pin)
   self.assertEqual(family_evidence(st,[identity(a)],dict(target,toolchain='other'),workload),[])
   st.rebuild();self.assertEqual(family_evidence(st,[identity(a)],target,workload),[obs])
   (st.data/'observations'/f'{ident}.json').write_bytes(canonical(dict(obs,metrics=dict(complete_call_ns=['1'],peak_bytes=0))))
   with self.assertRaisesRegex(ValueError,'content mismatch'):family_evidence(st,[identity(a)],target,workload)
 def test_structural_candidates_preserve_exhaustive_matches_and_dependency_closures(self):
  u=value('U32');seq=value({'List':'U32'});xs=var(seq,'input');f=var({'Arrow':[u,u]},'mapper')
  term=op(u,'call:foldl',op(seq,'method:map',xs,f),var(u,'seed'),var({'Arrow':[u,{'Arrow':[u,u]}]},'step'))
  subject={'functions':{'f':term}}
  rows=templates()
  with tempfile.TemporaryDirectory()as d:
   st=Store.publish(d,[r['object']for r in rows]);st.rebuild()
   actual=candidates(st,subject,'ink-semantic-law-template-v1')
   expected=[]
   for row in rows:
    law=row['object']['payload']['law']
    if list(TemplateSites(subject).matches(law['from'],law['params'],row['object']['payload']['type_parameters'])):expected.append(identity(row['object']))
   self.assertTrue(set(expected)<=set(actual));self.assertLess(len(actual),len(rows))
   # An old pin with no index retains full discovery.
   (Path(d)/'index.sqlite').unlink()
   self.assertEqual(len(candidates(st,subject,'ink-semantic-law-template-v1')),len(rows))

 def test_nested_discrimination_requires_one_matching_site_not_a_union(self):
  u=value('U32');x=var(u,'x');pattern=op(u,'call:outer',op(u,'call:left',x),op(u,'call:right',x))
  law=dict(params={'x':u},conditions=[],**{'from':pattern,'to':x},proof='Normalize')
  obj=entry('definition','ink-semantic-law-template-v1',dict(type_parameters=[],law=law,dependencies={}))
  subject={'functions':{'a':op(u,'call:outer',op(u,'call:left',x),x),'b':op(u,'call:outer',x,op(u,'call:right',x))}}
  with tempfile.TemporaryDirectory()as d:
   st=Store.publish(d,[obj]);st.rebuild();self.assertEqual(candidates(st,subject,obj['semantics']),[])
   subject['functions']['c']=pattern;self.assertEqual(candidates(st,subject,obj['semantics']),[identity(obj)])

 def test_pack_only_exports_identical_objects_and_authenticates_every_read(self):
  with tempfile.TemporaryDirectory()as d:
   a=entry('definition','test-v1',{'body':'a'});b=entry('definition','test-v1',{'body':'b'},[identity(a)])
   st=Store.publish(d,[a,b]);st.rebuild();before=st.bundle([identity(b)]);pin=st.snapshot_id
   receipt=pack(st);self.assertEqual(receipt['objects'],2)
   for file in (Path(d)/'store/objects').glob('*.json'):file.unlink()
   self.assertEqual(st.bundle([identity(b)]),before);self.assertEqual(Store(d).snapshot_id,pin)
   st.rebuild();self.assertEqual(st.bundle([identity(b)]),before)
   # Snapshot membership and SQLite keys cannot authorise altered bytes.
   with sqlite3.connect(st.data/'objects.pack.sqlite')as db:
    db.execute('UPDATE objects SET bytes=? WHERE id=?',(canonical({**a,'payload':{'body':'forged'}}),identity(a)))
   with self.assertRaisesRegex(ValueError,'content mismatch'):st.bundle([identity(b)])

 def test_pack_failure_preserves_prior_pack_and_loose_corruption_is_not_hidden(self):
  with tempfile.TemporaryDirectory()as d:
   a=entry('definition','test-v1',{'body':1});st=Store.publish(d,[a]);pack(st)
   packed=(st.data/'objects.pack.sqlite').read_bytes();path=st.data/'objects'/f'{identity(a)}.json';path.write_bytes(canonical({**a,'payload':{'body':2}}))
   with self.assertRaisesRegex(ValueError,'content mismatch'):pack(st)
   self.assertEqual((st.data/'objects.pack.sqlite').read_bytes(),packed)
   with self.assertRaisesRegex(ValueError,'content mismatch'):st.object(identity(a))
   self.assertEqual(list(st.data.glob('.ink-pack-*')),[])

 def test_selectors_and_independent_capabilities_are_data_with_bounded_composition(self):
  recipe=next(r for r in load()[0]['recipes']if r['id']=='literal-physical-alternatives')
  definitions={'a'*64:{'Datatype':dict(constructors=[dict(fields=[]),dict(fields=['U64','SelfType'])])},'b'*64:{'Function':dict(params=[['xs',{'Data':'a'*64}]],result='U64')}}
  ctx=dict(core={'program':dict(functions=[],states=[])},source='c'*64,representation={'representation':'d'*64},definitions=definitions,emit_target='rust')
  rows=list(physical(ctx,**recipe['parameters']));plans=[r['step']['package']for r in rows]
  self.assertTrue(any(p['packed_datatypes']and p['memo_functions']for p in plans))
  self.assertLessEqual(len(rows),recipe['parameters']['composition_limit'])
  self.assertFalse(matches({'has':[{'path':['subject']},{'literal':'Data'}]},'Bool'))
  with self.assertRaisesRegex(ValueError,'budget'):evaluate({'all':[{'literal':[1]*5000},{'literal':True}]},{})
  with self.assertRaisesRegex(ValueError,'unknown'):matches({'execute':[{'literal':'code'}]},{})
  # A broad packing domain cannot consume every proposal before memoisation
  # and mixed strategies receive a turn.
  ctx['definitions'].update({f'{n:064x}':definitions['a'*64]for n in range(300)})
  parameters=dict(recipe['parameters'],composition_limit=3)
  small=[r['step']['package']for r in physical(ctx,**parameters)]
  self.assertTrue(any(p['packed_datatypes']and p['memo_functions']for p in small))

 def test_imported_algorithm_reuses_helper_and_proof_and_kernel_rejects_false_parent(self):
  examples=json.loads((ROOT/'knowledge/libraries/source-algorithms.json').read_bytes());base=examples[0]['object'];bid=identity(base)
  law=copy.deepcopy(base['payload']['law']);law['to']['node']['Op'][0]='call:imported_unwrap'
  law['proof']={'Use':dict(law='$base',arguments={'xs':law['from']['node']['Op'][1][0]},premises=[])}
  payload=dict(type_parameters=['A'],definitions=dict(functions=[],ids=[],records={},enums={}),law=law,imports={'$base':dict(algorithm=bid,types={'A':{'Named':'$A'}},exports={'imported_unwrap':'unwrap'})})
  derived=entry('definition','ink-source-algorithm-v1',payload,[bid]);did=identity(derived)
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);st=Store.publish(d/'db',[base,derived]);st.rebuild()
   defs,_,support=resolve(st,payload,{'A':'U32'},did);self.assertEqual(len(defs['functions']),1);self.assertEqual(len(support),1)
   source=d/'source.ink';source.write_text('module Imports; pub fn f(xs:List<u32>)->List<u32>{return xs.map(fn(x)=>x);}')
   core=d/'core.json';r=subprocess.run([str(COMPILER),'emit-core',str(source),'-o',str(core)],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
   module=json.loads(core.read_text());ctx=dict(core=module,source=json.loads(r.stdout)['core_sha256'],compiler=str(COMPILER),knowledge_root=str(st.root),knowledge_snapshot=st.snapshot_id)
   rows=list(propose(ctx));candidate=next(r for r in rows if r['status']=='proposal'and r['label']==did)
   packet=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=ctx['source'],steps=candidate['steps']);path=d/'plan.json';path.write_bytes(canonical(packet))
   r=subprocess.run([str(COMPILER),'check-plan',str(core),str(path),'--core'],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
   # A false parent law still has genuine imported helpers and a genuine base.
   bad=copy.deepcopy(payload);bad['law']['to']=op(value({'List':{'Named':'$A'}}),'call:empty')
   broken=entry('definition','ink-source-algorithm-v1',bad,[bid]);badst=Store.publish(d/'bad',[base,broken]);ctx.update(knowledge_root=str(badst.root),knowledge_snapshot=badst.snapshot_id)
   candidate=next(r for r in propose(ctx)if r['status']=='proposal'and r['label']==identity(broken));packet['steps']=candidate['steps'];path.write_bytes(canonical(packet))
   r=subprocess.run([str(COMPILER),'check-plan',str(core),str(path),'--core'],capture_output=True,text=True);self.assertNotEqual(r.returncode,0)
