"""Reused contract certificates are replayed and retained without wrapper laws."""
import tempfile,unittest
from pathlib import Path
from unittest.mock import patch
from ink_knowledge import Store,semantic_entry,identity,entry
from producers.contract_proofs import author_obligations
from producers.semantic_laws import value,var

class Session:
 def __init__(self,status):self.status=status;self.calls=[]
 def check(self,name,proof,bundle):
  self.calls.append((name,proof,bundle))
  return dict(status=self.status,error='false supplied proof')

class ContractReplay(unittest.TestCase):
 def packet(self,directory):
  x=var(value('U32'),'x')
  law=dict(schema=1,semantics='ink-conditional-laws-v1',params={'x':x['sort']},conditions=[],**{'from':x,'to':x},proof='Normalize',dependencies=[])
  obj=semantic_entry(law);ident=identity(obj);store=Store.publish(directory/'original',[obj])
  proof={'Use':dict(law=ident,arguments={'x':x},premises=[])}
  goals=dict(semantics='ink-source-contracts-v1',source_sha256='0'*64,state=None,definition_context={},pure=[dict(name='id:ensures:0',params=law['params'],conditions=[],goal={'from':x,'to':x})])
  return goals,dict(proofs={'id:ensures:0':proof},knowledge=store.bundle([ident])),ident
 def test_direct_use_replays_before_reusing_the_original_object(self):
  with tempfile.TemporaryDirectory()as temporary:
   directory=Path(temporary);goals,supplied,ident=self.packet(directory);session=Session('checked')
   compiler=directory/'compiler';compiler.write_bytes(b'checker identity for transport test')
   with patch('producers.contract_proofs.subprocess.run'):
    evidence,bank=author_obligations(str(compiler),'source.ink',directory,None,[],goals,session,supplied)
   self.assertEqual(session.calls,[('id:ensures:0',supplied['proofs']['id:ensures:0'],supplied['knowledge'])])
   self.assertEqual(evidence['proofs'],supplied['proofs']);self.assertEqual(set(bank.members()),{ident})
 def test_rejected_supplied_proof_does_not_fall_back_or_publish(self):
  with tempfile.TemporaryDirectory()as temporary:
   directory=Path(temporary);goals,supplied,_=self.packet(directory);session=Session('rejected')
   with self.assertRaisesRegex(ValueError,'supplied pure proof failed replay'):
    author_obligations('compiler','source.ink',directory,None,[],goals,session,supplied)
   self.assertEqual(len(session.calls),1);self.assertFalse((directory/'evidence.json').exists())

 def state_packet(self,directory):
  theorem=dict(params=[['x','U64']],conditions=[],**{'from':{'Var':'x'},'to':{'Var':'x'}},proof={'Refl':{'Var':'x'}})
  obj=entry('theorem','first-order-inductive-equality-v1',{'declaration':{'Theorem':theorem}},parameters={'x':'U64'},conditions=[])
  ident=identity(obj);store=Store.publish(directory/'original',[obj]);proof={'Use':dict(theorem=ident,arguments=[{'Var':'x'}],premises=[])}
  goal=dict(name='observe:ensures:0',params=theorem['params'],conditions=[],goal={'from':{'Var':'x'},'to':{'Var':'x'}})
  goals=dict(semantics='ink-source-contracts-v1',source_sha256='0'*64,pure=[],state={'objects':{},'obligations':[goal]},definition_context={})
  return goals,dict(state_proofs={goal['name']:proof},state_knowledge=store.bundle([ident])),ident
 def test_state_use_replays_without_traversal_search_or_duplicate_wrappers(self):
  with tempfile.TemporaryDirectory()as temporary:
   directory=Path(temporary);goals,supplied,ident=self.state_packet(directory);session=Session('checked')
   with patch('producers.contract_proofs.subprocess.run'),patch('producers.contract_proofs.state_proof',side_effect=AssertionError('state search must not run')):
    evidence,bank=author_obligations('compiler','source.ink',directory,None,[],goals,session,supplied)
   self.assertEqual(session.calls,[('observe:ensures:0',supplied['state_proofs']['observe:ensures:0'],supplied['state_knowledge'])])
   self.assertEqual(evidence['state_proofs'],supplied['state_proofs']);self.assertEqual(set(bank.members()),{ident})
 def test_rejected_state_use_is_never_replaced_with_an_assumption(self):
  with tempfile.TemporaryDirectory()as temporary:
   directory=Path(temporary);goals,supplied,_=self.state_packet(directory);session=Session('rejected')
   with self.assertRaisesRegex(ValueError,'supplied state proof failed replay'):
    author_obligations('compiler','source.ink',directory,None,[],goals,session,supplied)
   self.assertEqual(len(session.calls),1);self.assertFalse((directory/'evidence.json').exists())
 def test_missing_state_obligations_still_get_fresh_proofs(self):
  import copy
  with tempfile.TemporaryDirectory()as temporary:
   directory=Path(temporary);goals,supplied,ident=self.state_packet(directory);session=Session('checked')
   missing=copy.deepcopy(goals['state']['obligations'][0]);missing['name']='additional:ensures:0';goals['state']['obligations'].append(missing)
   compiler=directory/'compiler';compiler.write_bytes(b'checker identity for transport test')
   with patch('producers.contract_proofs.subprocess.run'):
    evidence,bank=author_obligations(str(compiler),'source.ink',directory,None,[],goals,session,supplied)
   self.assertEqual(evidence['state_proofs']['observe:ensures:0'],supplied['state_proofs']['observe:ensures:0'])
   self.assertIn('additional:ensures:0',evidence['state_proofs']);self.assertGreater(len(bank.members()),1)
   self.assertEqual(session.calls[0][0],'observe:ensures:0');self.assertTrue(any(name=='additional:ensures:0'for name,_,_ in session.calls))
