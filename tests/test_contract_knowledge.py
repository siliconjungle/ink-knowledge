"""Contract proof closure is preserved through ordinary implementation packages."""
import tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,entry,identity
from ink_knowledge.implementation_candidates import identity_selection,publish_candidates,proof_views

class ContractKnowledge(unittest.TestCase):
 def test_nested_refinement_imports_both_proof_domains(self):
  with tempfile.TemporaryDirectory() as temporary:
   root=Path(temporary);law=entry('definition','test-data',{'law':1});theorem=entry('definition','test-data',{'theorem':2})
   store=Store.publish(root,[law,theorem]);package=identity_selection('1'*64)
   package['contract_refinement']={'bodies':{},'evidence':{'knowledge':store.bundle([identity(law)]),'state_knowledge':store.bundle([identity(theorem)])}}
   composed={'schema':1,'semantics':'ink-compiled-plan-v1','input_core_sha256':'1'*64,'steps':[{'kind':'rewrite','package':package}]}
   self.assertEqual(len(list(proof_views(composed))),3)
   published,ids=publish_candidates(root,[composed]);self.assertEqual(set(published.object(ids[0])['dependencies']),{identity(law),identity(theorem)})
   self.assertEqual(set(published.bundle(ids)['objects']),{ids[0],identity(law),identity(theorem)})

 def test_published_contract_laws_have_no_helper_certificates(self):
  root=Path(__file__).resolve().parents[1];store=Store(root);names=__import__('json').loads((root/'store/names.json').read_text())
  for name in ['contracts.zero-map-u64','contracts.identity-map-u32','contracts.sorted-identity-u64','contracts.unique-id-check-erasure']:
   law=store.object(names[name]);self.assertEqual(law['kind'],'rewrite');self.assertFalse(law['payload']['definition_context']['definitions'])

 def test_collection_source_laws_are_published(self):
  root=Path(__file__).resolve().parents[1];store=Store(root);names=__import__('json').loads((root/'store/names.json').read_text())
  for name in ['bag_condition','bag_multiplicity','identity_map','sorted_identity','unique_id_check_erasure','zero_map']:
   law=store.object(names['contract-laws/'+name]);self.assertEqual(law['kind'],'rewrite')

 def test_state_theorems_have_authenticated_closures(self):
  root=Path(__file__).resolve().parents[1];store=Store(root);names=__import__('json').loads((root/'store/names.json').read_text())
  for name in ['invariant:0:initial','replace_all:invariant:0','replace_all:ensures:0','clear:invariant:0']:
   ident=names['contracts.state-list.'+name];obj=store.object(ident)
   self.assertEqual(obj['kind'],'theorem');self.assertIn(ident,store.bundle([ident])['objects'])

if __name__=='__main__':unittest.main()
