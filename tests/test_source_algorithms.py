import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_knowledge.source_algorithms import instantiate,namespace,publish,proof_roots,SEMANTICS
from ink_knowledge.recipes import load,role
from producers.capacity_plans import expression
from producers.semantic_laws import value,var,op,bound,law
class DatabaseAlgorithms(unittest.TestCase):
 def test_incremental_transport_preserves_old_and_new_external_dependencies(self):
  x=var(value('U32'),'x');old=semantic_entry(law({'x':value('U32')},x,x));oid=identity(old)
  derived=semantic_entry(law({'x':value('U32')},x,x,{'Use':{'law':oid,'arguments':{'x':x},'premises':[]}},dependencies=[oid]));did=identity(derived)
  second=semantic_entry(law({'x':value('U32')},x,x,{'Use':{'law':did,'arguments':{'x':x},'premises':[]}},dependencies=[did]));sid=identity(second)
  with tempfile.TemporaryDirectory() as temporary:
   d=Path(temporary);store=Store.publish(d/'knowledge',[old,derived])
   view=ProposalViews(store,{},d/'transport');view.update({sid:second})
   self.assertEqual(set(view.bundle([sid])['membership']),{oid,did,sid})
   fresh=semantic_entry(law({'x':value('U32')},op(value('U32'),'binary:+',x,x),op(value('U32'),'binary:*',x,{'sort':value('U32'),'node':{'Word':2}})))
   view.update({identity(fresh):fresh})
   self.assertEqual(set(view.bundle([sid])['membership']),{oid,did,sid})
 def test_new_proof_can_reuse_published_law_with_checked_membership(self):
  x=var(value('U32'),'x');old=semantic_entry(law({'x':value('U32')},x,x));oid=identity(old)
  new=semantic_entry(law({'x':value('U32')},x,x,{'Use':{'law':oid,'arguments':{'x':x},'premises':[]}},dependencies=[oid]));nid=identity(new)
  compiler=Path(os.environ.get('INK_COMPILER',Path(__file__).resolve().parents[2]/'target/debug/ink'))
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);store=Store.publish(d/'knowledge',[old]);view=ProposalViews(store,{nid:new},d/'transport').bundle([nid]);self.assertEqual(set(view['membership']),{oid,nid})
   source=d/'source.ink';source.write_text('module proof_transport;fn id(x:u32)->u32{return x;}');core=d/'core.json';packet=d/'view.json';packet.write_bytes(canonical(view))
   subprocess.run([compiler,'emit-core',source,'-o',core],check=True,capture_output=True)
   checked=subprocess.run([compiler,'knowledge-check',core,packet],capture_output=True,text=True);self.assertEqual(checked.returncode,0,checked.stderr)
 def test_replacement_proofs_keep_original_endpoints_and_intermediate_unfolds(self):
  core={'program':{'functions':[{'name':n}for n in ['old','fresh','intermediate']]}}
  term=lambda name:op(value('U32'),'call:'+name)
  law={'from':term('old'),'to':term('fresh'),'conditions':[],'proof':{'Trans':{'middle':term('intermediate'),'left':'Unfold','right':'Normalize'}},'definition_context':{'unused':term('not_available')}}
  self.assertEqual(proof_roots(core,law,['fresh']),['fresh','intermediate','old'])
 def examples(self):return json.loads((Path(__file__).resolve().parents[1]/'libraries/source-algorithms.json').read_bytes())
 def test_fresh_names_and_type_substitution_do_not_rename_literals_or_fields(self):
  obj=self.examples()[0]['object'];definitions,law=instantiate(obj['payload'],{'A':'U32'},'a'*64)
  name=definitions['functions'][0]['name'];self.assertTrue(name.startswith('db_'));self.assertEqual(definitions['functions'][0]['result'],{'List':'U32'});self.assertEqual(law['to']['node']['Op'][0],'call:'+name)
  self.assertNotIn('$A',str(definitions));self.assertEqual(definitions['functions'][0]['body']['Field'][1],'value')
  self.assertEqual(namespace({'String':'Frame'},{'Frame':'fresh'}),{'String':'Frame'});self.assertEqual(namespace({'Var':'Flag.Yes'},{'Flag':'fresh'}),{'Var':'fresh.Yes'})
 def test_qualified_globals_are_renamed_without_capturing_lexical_bindings(self):
  field={'Field':[{'Var':'Flag'},'Yes']};names={'Flag':'fresh','Frame':'scratch'}
  self.assertEqual(namespace(field,names),{'Field':[{'Var':'fresh'},'Yes']})
  self.assertEqual(namespace({'Lambda':['Flag',field]},names),{'Lambda':['Flag',field]})
  self.assertEqual(namespace({'Let':['Flag',None,field,field]},names),{'Let':['Flag',None,{'Field':[{'Var':'fresh'},'Yes']},field]})
  f=dict(name='run',params=[['Flag','U32']],result='U32',body=field);self.assertEqual(namespace(f,names)['body'],field)
  self.assertEqual(namespace({'Op':['record:Frame',[]]},names),{'Op':['record:scratch',[]]})
 def test_publication_is_snapshot_owned_data_with_an_installed_generic_recipe(self):
  with tempfile.TemporaryDirectory()as d:
   Store.publish(d,[],{});store=publish(d,self.examples());self.assertEqual(len(store.query(kind='definition',semantics=SEMANTICS)),4)
   self.assertEqual(role(store.object(store.query(kind='definition',semantics=SEMANTICS)[0])),'source-algorithm-discovery')
  self.assertTrue(any(r['id']=='database-source-algorithms'for r in load()[0]['recipes']))
  bad=copy.deepcopy(self.examples());bad[0]['object']['semantics']='unknown'
  with tempfile.TemporaryDirectory()as d:
   Store.publish(d,[],{})
   with self.assertRaises(ValueError):publish(d,bad)
 def test_arbitrary_capacity_arithmetic_and_calls_are_reified_without_formula_cases(self):
  seq=value({'List':'U32'});capacity=op(value('Int'),'binary:+',op(value('Int'),'call:count',var(seq,'xs')),op(value('Int'),'call:count',var(seq,'ys')))
  self.assertEqual(expression(capacity,{'xs','ys'}),{'Binary':['+',{'Call':['count',[{'Var':'xs'}]]},{'Call':['count',[{'Var':'ys'}]]}]})
  with self.assertRaises(ValueError):expression(bound(value('Int'),0),{'xs'})
  with self.assertRaises(ValueError):expression(var(value('Int'),'unbound'),{'xs'})
if __name__=='__main__':unittest.main()
