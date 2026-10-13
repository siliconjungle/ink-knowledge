"""Checker transport rejects malformed proposals without granting authority."""
import io,json,unittest
from unittest.mock import patch
from producers.contract_proofs import ProofSession
class Process:
 def __init__(self,answers):
  self.stdin=io.StringIO();self.stdout=io.StringIO(''.join(json.dumps(x)+'\n' for x in answers));self.stderr=io.StringIO()
 def wait(self):return 0
class ContractSession(unittest.TestCase):
 def test_schema_rejection_does_not_poison_the_next_checked_attempt(self):
  replies=[dict(status='ready',source_sha256='source'),dict(status='rejected',error='recursion limit exceeded'),dict(status='checked',name='actual')]
  with patch('producers.contract_proofs.subprocess.Popen',return_value=Process(replies)):
   with ProofSession('compiler','source',[],'source') as session:
    self.assertEqual(session.check('actual',{},None)['status'],'rejected')
    self.assertEqual(session.check('actual','Normalize',None)['status'],'checked')
 def test_wrong_source_or_wrong_checked_obligation_never_passes(self):
  with patch('producers.contract_proofs.subprocess.Popen',return_value=Process([dict(status='ready',source_sha256='different')])):
   with self.assertRaisesRegex(ValueError,'source identity'):ProofSession('compiler','source',[],'source').__enter__()
  replies=[dict(status='ready',source_sha256='source'),dict(status='checked',name='different')]
  with patch('producers.contract_proofs.subprocess.Popen',return_value=Process(replies)):
   with ProofSession('compiler','source',[],'source') as session:
    with self.assertRaisesRegex(ValueError,'obligation differs'):session.check('actual','Normalize',None)
