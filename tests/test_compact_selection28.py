"""Real checker/compact orchestration, mixed definition contexts and old laws."""
import importlib.util,json,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path[:0]=[str(ROOT/'knowledge'),str(ROOT/'planner')]
from ink_knowledge import Store
spec=importlib.util.spec_from_file_location('compact28',ROOT/'bench/compact_selection28.py')
compact=importlib.util.module_from_spec(spec);spec.loader.exec_module(compact)
R=ROOT/'reports/web-engine-28-2026-10-11'
COMPILER=ROOT.parent/'toolchain/ink-web-engine-28-rc1'
MODEL=ROOT/'reports/web-stack-proofs-27-2026-10-11/cpu-cost-model.json'
@unittest.skipUnless((R/'context/candidate-view.json').is_file()and COMPILER.is_file()and MODEL.is_file(),
 'requires the archived web-engine-28 benchmark fixture and frozen compiler')
class CompactContexts(unittest.TestCase):
 def test_mixed_valid_contexts_do_not_poison_admission(self):
  store=Store(R/'context/candidate-store')
  rows=json.loads((R/'context/candidate-rows.json').read_text())
  # Check both modules: the incompatible sibling remains valid portable math,
  # but cannot be imported into this module's selection catalogue.
  with tempfile.TemporaryDirectory() as tmp:
   for variant in ['primary','heldout']:
    result=compact.plan(COMPILER,R/f'context/u32-{variant}-input.core.json',store,MODEL,Path(tmp)/f'{variant}.json',64)
    ctx=result['orchestration']['context_applicability']
    name=f'context_composed_mapfusion_{variant}_u32'
    wanted=next(row['id'] for row in rows if row['name']==name)
    other=next(row['id'] for row in rows if row['name']==f'context_composed_mapfusion_{"heldout" if variant=="primary" else "primary"}_u32')
    self.assertIn(wanted,ctx['retained_roots']);self.assertIn(other,ctx['excluded_roots'])
    self.assertIn('selected_core_sha256',result['check']);self.assertTrue(any(row['roots'] and row['exit_code']==0 for row in result['orchestration']['selection_checks']))
    # Cached reuse must still replay the exact checked package.
    self.assertEqual(compact.plan(COMPILER,R/f'context/u32-{variant}-input.core.json',store,MODEL,Path(tmp)/f'{variant}.json',64),result)
 def test_context_free_catalogue_compatibility(self):
  entries=json.loads((R/'context/candidate-view.json').read_text())['objects']
  old=[entry for entry in entries.values() if not entry['payload'].get('definition_context')]
  with tempfile.TemporaryDirectory() as tmp:
   store=Store.publish(Path(tmp)/'store',old)
   result=compact.plan(COMPILER,R/'context/u32-primary-input.core.json',store,MODEL,Path(tmp)/'selection.json',64)
   ctx=result['orchestration']['context_applicability']
   self.assertEqual(ctx['excluded_roots'],[])
   self.assertEqual(ctx['retained_roots'],ctx['discovered_roots'])
   self.assertIn('selected_core_sha256',result['check']);self.assertTrue(any(row['roots'] and row['exit_code']==0 for row in result['orchestration']['selection_checks']))
if __name__=='__main__':unittest.main()
