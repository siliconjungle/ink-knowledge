"""Training-only view association never decodes the full heldout sample file."""
import json
import sys
import tempfile
import unittest
from pathlib import Path
K=Path(__file__).resolve().parents[1];sys.path[:0]=[str(K),str(K.parent/'planner')]
from producers.target_work40_labels import training_view
from ink_planner.physical_features import file_hash


class RestrictedLabelsTests(unittest.TestCase):
    def fixture(self,root):
        meta=dict(bindings={},protocol=dict(rounds=5));(root/'metadata.json').write_text(json.dumps(meta));(root/'spec.json').write_text('{}')
        # Non-JSON raw bytes prove the training view does not decode heldout values.
        (root/'node-results.json').write_text('opaque audited heldout sample bytes')
        frames=[dict(id=str(i),timed=True,split='train')for i in range(48)]+[dict(id='heldout',timed=True,split='heldout-family')]
        (root/'fixtures.json').write_text(json.dumps(dict(frames=frames)))
        audit=dict(bindings=dict(results=file_hash(root/'node-results.json')));(root/'node-audit.json').write_text(json.dumps(audit))
        view=dict(schema=1,kind='general40-audited-training-view-v1',status='passed',source_bindings={name:file_hash(root/name)for name in('metadata.json','spec.json','fixtures.json','node-results.json','node-audit.json')},metadata_sha256=file_hash(root/'metadata.json'),prepared_bindings={},protocol=meta['protocol'],frames=sorted(str(i)for i in range(48)),samples=[dict(frame='0',split='train',ns_per_call=.125)])
        p=root/'view.json';p.write_text(json.dumps(view));return meta,audit,p,view
    def test_restricted_view_reads_no_full_raw_sample_values(self):
        with tempfile.TemporaryDirectory()as d:
            r=Path(d);m,a,p,v=self.fixture(r);self.assertEqual(training_view(r,p,m,a),v)
    def test_heldout_rows_and_source_drift_rejected(self):
        with tempfile.TemporaryDirectory()as d:
            r=Path(d);m,a,p,v=self.fixture(r);v['samples'].append(dict(frame='heldout',split='heldout-family',ns_per_call=7));p.write_text(json.dumps(v))
            with self.assertRaisesRegex(ValueError,'heldout row'):training_view(r,p,m,a)
            m,a,p,v=self.fixture(r);(r/'node-results.json').write_text('changed')
            with self.assertRaisesRegex(ValueError,'source drift'):training_view(r,p,m,a)
    def test_wrong_protocol_and_missing_training_cell_rejected(self):
        with tempfile.TemporaryDirectory()as d:
            r=Path(d);m,a,p,v=self.fixture(r);v['protocol']={'rounds':4};p.write_text(json.dumps(v))
            with self.assertRaisesRegex(ValueError,'metadata association'):training_view(r,p,m,a)
            m,a,p,v=self.fixture(r);v['frames'].pop();p.write_text(json.dumps(v))
            with self.assertRaisesRegex(ValueError,'coverage'):training_view(r,p,m,a)
if __name__=='__main__':unittest.main()
