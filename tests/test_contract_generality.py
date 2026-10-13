"""Bounded witness policy, binder hygiene, and source-domain discovery."""
import json,unittest
from producers.contract_search import witnesses
from producers.semantic_observations import opened
from producers.semantic_laws import value,term,bound,lam
from producers.contract_algebra import templates
from ink_knowledge import semantic_entry,identity,entry
from ink_knowledge.recipes import role

class GeneralContracts(unittest.TestCase):
 def spec(self,result='U32',params=None,ensures=None,kind=None):
  return dict(name='arbitrary',result=result,params=params or [],requires=[],ensures=ensures or [],kind=kind)
 def test_alternatives_and_inequality_boundaries_are_candidates(self):
  spec=self.spec(ensures=[{'Binary':['||',{'Binary':['==',{'Var':'result'},{'Num':1}]},{'Binary':['==',{'Var':'result'},{'Num':2}]}]}])
  found=list(witnesses({'functions':[]},spec));self.assertIn({'Pure':{'Num':1}},found);self.assertIn({'Pure':{'Num':2}},found)
  spec=self.spec('Int',[['n','Int']],[{'Binary':['<',{'Var':'result'},{'Var':'n'}]}])
  found=list(witnesses({'functions':[]},spec));self.assertIn({'Pure':{'Binary':['-',{'Var':'n'},{'Num':1}]}},found)
 def test_typed_functions_and_named_bodies_are_bounded(self):
  spec=self.spec('U32',[['x','U32']]);program=dict(functions=[dict(name='helper',params=[['value','U32']],result='U32',body={'Var':'value'})],contracts=dict(implementations=[]))
  self.assertIn({'Pure':{'Call':['helper',[{'Var':'x'}]]}},list(witnesses(program,spec)))
  spec['kind']='Query';program['contracts']['implementations']=[dict(name=str(i),specification='arbitrary',body=[{'Return':{'Num':i}}])for i in range(100)]
  self.assertLessEqual(len(list(witnesses(program,spec,3))),3)
  with self.assertRaises(ValueError):list(witnesses(program,spec,0))
 def test_opening_preserves_inner_binders_and_rejects_escape(self):
  scalar=value('U32');scope=[('outer',scalar)]
  self.assertEqual(opened(lam(scalar,bound(scalar,1)),scope)['node']['Lambda'],term(scalar,{'Free':'outer'}))
  self.assertEqual(opened(lam(scalar,bound(scalar,0)),scope),lam(scalar,bound(scalar,0)))
  with self.assertRaises(ValueError):opened(bound(scalar,1),scope)
 def test_templates_do_not_retain_erased_empty_general_fields(self):
  scalar=value({'Named':'T'});x=term(scalar,{'Free':'x'})
  law=dict(schema=1,semantics='ink-general-laws-v1',types=['T'],params={'x':scalar},assumptions=[],conditions=[],**{'from':x,'to':x},proof='Normalize',dependencies=[])
  obj=semantic_entry(law);objects,mapping=templates({identity(obj):obj});generated=next(iter(objects.values()))['payload']['law']
  self.assertNotIn('types',generated);self.assertNotIn('assumptions',generated)
  self.assertEqual(generated['from']['sort'],value({'Named':'$T'}))
  self.assertEqual(len(mapping),1)
 def test_general_laws_and_invariant_representations_are_discoverable(self):
  self.assertEqual(role(entry('rewrite','ink-general-laws-v1',{})),'general-proof-dependency')
  self.assertEqual(role(entry('representation','ink-source-representation-v2',{})),'representation-search')
 def test_contract_variants_are_proposals_with_fresh_payloads(self):
  from producers.contract_proofs import pure_proposals,proof_semantics
  scalar=value('U32');x=term(scalar,{'Free':'contract_payload_0'})
  goal=dict(params={'value':value({'Result':['U32','U32']}),'contract_payload_0':scalar},conditions=[],goal={'from':x,'to':x})
  proposal=next(p for p in pure_proposals(goal) if isinstance(p,dict) and 'Variants' in p)
  self.assertEqual(proposal['Variants']['names'],['contract_payload_0_','contract_payload_1'])
  self.assertEqual(proof_semantics(proposal),'ink-general-laws-v1')
  nested={'Cases':dict(condition=term(value('Bool'),{'Bool':True}),on_false='Normalize',on_true=proposal)}
  self.assertEqual(proof_semantics(nested),'ink-general-laws-v1')
  self.assertEqual(proof_semantics({'Use':dict(law='0'*64,arguments={},premises=['Normalize'])}),'ink-conditional-laws-v1')
  self.assertEqual(proof_semantics({'Use':dict(law='0'*64,arguments={},premises=[],types={'T':'U32'})}),'ink-general-laws-v1')

if __name__=='__main__':unittest.main()
