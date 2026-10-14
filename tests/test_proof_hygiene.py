"""Composed proof terms retain lexical meaning without binder shadowing."""
import unittest
from producers.equational import fresh_alpha as alpha
from producers.proof_composition import freshen_match_terms
from producers.point_delta import free_variables

def matched(name,body):
 return {'Match':dict(scrutinee={'Var':'input'},branches=[dict(bindings=[name],body=body)])}

class ProofHygiene(unittest.TestCase):
 def test_alpha_does_not_capture_a_free_generated_name(self):
  t=matched('x',{'Binary':dict(op='+',left={'Var':'x'},right={'Var':'eq_bound_0_0'})})
  result=alpha(t);self.assertEqual(free_variables(result),{'input','eq_bound_0_0'})
  self.assertNotEqual(result['Match']['branches'][0]['bindings'],['eq_bound_0_0'])
  self.assertEqual(alpha(result),result)
 def test_nested_shadowing_is_freshened_with_its_lexical_references(self):
  t=matched('same',matched('same',{'Var':'same'}));result=alpha(t)
  outer=result['Match']['branches'][0];inner=outer['body']['Match']['branches'][0]
  self.assertNotEqual(outer['bindings'],inner['bindings']);self.assertEqual(inner['body'],{'Var':inner['bindings'][0]})
  self.assertEqual(free_variables(result),{'input'})
 def test_case_and_substitution_scopes_are_reserved_even_when_unused(self):
  t=matched('old',{'Var':'old'});proof={'Cases':dict(variable='input',**{'from':{'Var':'input'},'to':{'Var':'input'}},cases=[dict(bindings=['eq_bound_0_0'],proof={'Substitute':dict(variable='eq_bound_0_0_0',context=t,equality={'Convert':{'from':t,'to':t}})})])}
  result=freshen_match_terms(proof,['ambient']);case=result['Cases']['cases'][0];sub=case['proof']['Substitute']
  self.assertEqual(case['bindings'],['eq_bound_0_0']);self.assertEqual(sub['variable'],'eq_bound_0_0_0')
  self.assertEqual(sub['context']['Match']['branches'][0]['bindings'],['eq_bound_0_0_1'])
  self.assertEqual(sub['equality']['Convert']['from']['Match']['branches'][0]['bindings'],['eq_bound_0_0_0'])
  self.assertEqual(freshen_match_terms(result,['ambient']),result)
