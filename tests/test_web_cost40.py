"""Synthetic fits validate fixed protocol mechanics, never speed claims."""
import copy,json,math,sys,tempfile,unittest
from pathlib import Path
K=Path(__file__).resolve().parents[1];sys.path.insert(0,str(K))
from producers.web_cost40 import fit,evaluate,write,identity
from ink_planner.physical_features import file_hash

class PhysicalCalibrationTests(unittest.TestCase):
    def test_deterministic_nonnegative_relative_fit(self):
        xs=[dict(a=1,b=n)for n in(0,1,2,7,33)];ys=[3+2*x['b']for x in xs]
        a=fit(xs,ys,['a','b']);b=fit(xs,ys,['a','b']);self.assertEqual(a,b);self.assertEqual(a['rank'],2)
        self.assertAlmostEqual(a['weights']['a'],3,places=5);self.assertAlmostEqual(a['weights']['b'],2,places=5)
    def test_low_rank_and_missing_support_are_retained(self):
        xs=[dict(a=1,b=2,c=0)for _ in range(5)];r=fit(xs,[7]*5,['a','b','c'])
        self.assertEqual(r['rank'],1);self.assertTrue(r['low_rank']);self.assertIn('c',r['zero_support']);self.assertEqual(set(r['unidentified']),{'b','c'})
    def test_invalid_times_and_price_overflow_fail_without_clipping(self):
        for y in(True,0,-1,float('nan'),float('inf')):
            with self.subTest(y=y),self.assertRaises(ValueError):fit([dict(a=1)],[y],['a'])
        with self.assertRaises(ValueError):fit([dict(a=1)],[1e20],['a'])
    def test_frozen_predictions_evaluate_losses_without_refitting(self):
        with tempfile.TemporaryDirectory()as d:
            r=Path(d);f=r/'freeze';f.mkdir();cohort=dict(target='javascript',host=dict(engine='node',version='test'),boundary='owned',emitter_sha256='1'*64,entry_abi='test');fits={'a':dict(cohort=cohort)}
            base=dict(id='base',operation='branch',size=512,split='heldout-family',version='baseline',cohort='a',prediction_ns=5,unavailable=None,entry='entry',fixture_id='frame',fixture_sha256='2'*64,source_sha256='3'*64)
            candidate=dict(base,id='candidate',version='candidate',prediction_ns=1)
            write(f/'fits.json',fits);write(f/'predictions.json',[base,candidate]);write(f/'freeze.json',dict(status='frozen_before_heldout_evaluation',models={},fits_sha256=file_hash(f/'fits.json'),predictions_sha256=file_hash(f/'predictions.json')))
            heldout=dict(schema=1,kind='ink-target-work-heldout-v1',freeze_sha256=file_hash(f/'freeze.json'),sources=[],rows=[dict(feature_id='base',round=i,ns_per_call=2)for i in range(5)]+[dict(feature_id='candidate',round=i,ns_per_call=8)for i in range(5)])
            write(r/'heldout.json',heldout);before=file_hash(f/'predictions.json');result=evaluate(f,r/'heldout.json',r/'eval');self.assertEqual(result['losses'],1);self.assertEqual(result['choices'][0]['regret_relative'],3);self.assertEqual(file_hash(f/'predictions.json'),before)
            (f/'predictions.json').write_text('[]')
            with self.assertRaisesRegex(ValueError,'drift'):evaluate(f,r/'heldout.json',r/'bad')
if __name__=='__main__':unittest.main()
