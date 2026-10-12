import copy,json,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store
from ink_knowledge.source_algorithms import instantiate,namespace,publish,SEMANTICS
from ink_knowledge.recipes import load,role
from producers.capacity_plans import expression
from producers.semantic_laws import value,var,op,bound
class DatabaseAlgorithms(unittest.TestCase):
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
