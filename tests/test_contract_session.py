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

class ExportedSession(unittest.TestCase):
 def test_export_is_bound_to_ready_identity_and_uses_one_process(self):
  import tempfile
  from pathlib import Path
  from producers.contract_proofs import author
  with tempfile.TemporaryDirectory() as tmp:
   directory=Path(tmp);export=directory/'obligations.json'
   export.write_text('{"source_sha256":"stale"}')
   goals=dict(source_sha256='source',pure=[],state=None,definition_context={})
   def spawn(arguments,**kwargs):
    self.assertFalse(export.exists(),'previous export must not survive startup')
    self.assertIn('--export-obligations',arguments)
    export.write_text(json.dumps(goals))
    return Process([dict(status='ready',source_sha256='source')])
   with patch('producers.contract_proofs.subprocess.Popen',side_effect=spawn) as popen, patch('producers.contract_proofs.subprocess.run',side_effect=AssertionError('separate export process')), patch('producers.contract_proofs.author_obligations',return_value='authored') as compose:
    self.assertEqual(author('compiler',directory/'source.ink',directory),'authored')
    self.assertEqual(popen.call_count,1)
    self.assertEqual(compose.call_args.args[5],goals)
 def test_mismatched_export_cannot_start_authoring(self):
  import tempfile
  from pathlib import Path
  with tempfile.TemporaryDirectory() as tmp:
   export=Path(tmp)/'goals.json'
   def spawn(*args,**kwargs):
    export.write_text('{"source_sha256":"different"}')
    return Process([dict(status='ready',source_sha256='source')])
   with patch('producers.contract_proofs.subprocess.Popen',side_effect=spawn):
    with self.assertRaisesRegex(ValueError,'source identity'):ProofSession('compiler','source',[],export=export).__enter__()
 def test_failed_export_does_not_reuse_a_stale_file(self):
  import tempfile
  from pathlib import Path
  with tempfile.TemporaryDirectory() as tmp:
   export=Path(tmp)/'goals.json';export.write_text('{"source_sha256":"source"}')
   with patch('producers.contract_proofs.subprocess.Popen',return_value=Process([dict(status='ready',source_sha256='source')])):
    with self.assertRaises(FileNotFoundError):ProofSession('compiler','source',[],export=export).__enter__()
