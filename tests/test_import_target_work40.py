"""Canonical diagnostic import preserves exact evidence, never theorem authority."""
import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path
K=Path(__file__).resolve().parents[1];sys.path[:0]=[str(K),str(K.parent/'planner')]
from producers.import_target_work40 import collect, trace_entry
from producers.web_cost40 import write
from ink_knowledge.store import canonical, validate_entry, identity
from ink_planner.physical_features import file_hash, PhysicalPrices


class PhysicalImportTests(unittest.TestCase):
    def test_fractional_samples_and_target_scope_survive_canonical_data(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);write(root/'selection.json',dict(knowledge=dict(roots=['1'*64])))
            obs=dict(cohort=dict(target='javascript',host=dict(engine='node',version='test'),boundary='captured-js-owned',emitter_sha256='2'*64,entry_abi='test'),entry='entry',fixture_id='frame',components=dict(invocations=1,loop_iterations=17,allocation_events=3,copy_bytes=28),known=dict(invocations=True,loop_iterations=True,allocation_events=True,copy_bytes=True),unknown=[],bindings=dict(selection=dict(path='selection.json',sha256=file_hash(root/'selection.json')),selected_core=dict(sha256='3'*64),fixture=dict(sha256='4'*64)),scope='Synthetic untimed trace test')
            feature=dict(observation=obs,sidecar=str(root/'sidecar.json'),operation='compaction',size=64,split='train')
            obj,measured=trace_entry(feature,[.125,1.5,2.75,3.125,4.5],dict(labels_sha256=['5'*64]))
            validate_entry(obj);canonical(obj);self.assertEqual(obj['kind'],'definition');self.assertEqual(obj['semantics'],'ink-target-work-measurement-v1')
            self.assertEqual(obj['payload']['timing_ns_decimal_strings'],['0.125','1.5','2.75','3.125','4.5'])
            self.assertEqual(obj['dependencies'],['1'*64]);self.assertEqual(measured['entries'],['1'*64]);self.assertIsNone(measured['metrics']['peak_bytes'])
            changed=copy.deepcopy(feature);changed['observation']['cohort']['boundary']='into';other,_=trace_entry(changed,[.125,1.5,2.75,3.125,4.5],dict(labels_sha256=['5'*64]));self.assertNotEqual(identity(obj),identity(other))

    def fixture(self,root):
        write(root/'features.json',[]);write(root/'labels.json',dict(schema=1,kind='ink-target-work-training-v1',protocol_sha256='6'*64,sources=[],rows=[]))
        f=root/'frozen';model=dict(schema=1,kind='ink-target-work-prices-v1',cohort=dict(target='javascript',host=dict(engine='node',version='test'),boundary='owned',emitter_sha256='2'*64,entry_abi='test'),weights=dict(invocations=.125,loop_iterations=.375),training=dict(protocol_sha256='6'*64,observations_sha256='7'*64,scope='Synthetic fit test'))
        write(f/'models/m.json',model);write(f/'fits.json',{});write(f/'predictions.json',[])
        write(f/'freeze.json',dict(status='frozen_before_heldout_evaluation',fits_sha256=file_hash(f/'fits.json'),predictions_sha256=file_hash(f/'predictions.json'),models={'models/m.json':file_hash(f/'models/m.json')}))
        return f,model

    def test_price_exact_json_bytes_and_fractional_weights_roundtrip(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);f,model=self.fixture(root);objects,observations,names=collect(root/'features.json',[root/'labels.json'],f)
            self.assertEqual(observations,[]);self.assertEqual(len(objects),1);obj=objects[0];validate_entry(obj);canonical(obj)
            self.assertEqual(obj['payload']['model_json'],(f/'models/m.json').read_text());decoded=json.loads(obj['payload']['model_json']);PhysicalPrices(decoded);self.assertEqual(decoded,model)
            self.assertEqual(obj['dependencies'],[]);self.assertEqual(list(names.values()),[identity(obj)])

    def test_changed_models_and_label_sources_fail_closed(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);f,_=self.fixture(root);(f/'models/m.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'model bytes drift'):collect(root/'features.json',[root/'labels.json'],f)
            write(root/'source.json',{});labels=json.loads((root/'labels.json').read_text());labels['sources']=[dict(path='source.json',sha256=file_hash(root/'source.json'))];(root/'labels.json').write_text(json.dumps(labels));(root/'source.json').write_text('changed')
            with self.assertRaisesRegex(ValueError,'provenance drift'):collect(root/'features.json',[root/'labels.json'])


if __name__=='__main__':unittest.main()
