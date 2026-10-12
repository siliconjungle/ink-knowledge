import unittest
from producers.point_delta import sub,normal,free_variables
class Hygiene(unittest.TestCase):
 def test_substitution_respects_shadowing_and_cannot_capture(self):
  term={'Match':{'scrutinee':{'Var':'input'},'branches':[{'bindings':['x'],'body':{'Binary':{'op':'+','left':{'Var':'x'},'right':{'Var':'outer'}}}}]}}
  result=sub(term,{'x':{'U64':7},'outer':{'Var':'x'}})
  self.assertEqual(free_variables(result),{'input','x'})
  branch=result['Match']['branches'][0];self.assertNotEqual(branch['bindings'],['x']);self.assertEqual(branch['body']['Binary']['left'],{'Var':branch['bindings'][0]});self.assertEqual(branch['body']['Binary']['right'],{'Var':'x'})
 def test_unused_match_names_have_an_idempotent_common_normal_form(self):
  term=lambda name:{'Match':{'scrutinee':{'Var':'input'},'branches':[{'bindings':[name],'body':{'Bool':True}}]}}
  a=normal(term('ignored_a'),{});b=normal(term('ignored_b'),{})
  self.assertEqual(a,b);self.assertEqual(normal(a,{}),a)
 def test_unused_names_do_not_shadow_nested_match_bindings(self):
  term={'Match':{'scrutinee':{'Var':'input'},'branches':[{'bindings':['ignored'], 'body':{'Match':{'scrutinee':{'Var':'other'},'branches':[{'bindings':['unused_binding_0_0'],'body':{'Bool':True}}]}}}]}}
  result=normal(term,{})['Match']['branches'][0]
  self.assertNotEqual(result['bindings'],['unused_binding_0_0'])
  self.assertEqual(normal(normal(term,{}),{}),normal(term,{}))
 def test_substitution_avoids_nested_binder_shadowing_in_argument(self):
  inner={'Match':{'scrutinee':{'Var':'other'},'branches':[{'bindings':['x'],'body':{'Var':'x'}}]}}
  outer={'Match':{'scrutinee':{'Var':'input'},'branches':[{'bindings':['x'],'body':{'Var':'argument'}}]}}
  result=sub(outer,{'argument':inner})['Match']['branches'][0]
  self.assertNotEqual(result['bindings'],['x'])
  self.assertEqual(result['body'],inner)
if __name__=='__main__':unittest.main()
