"""Universal direct column point proofs, reproduction and false-proof control."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'producers'))
sys.path.insert(0,str(ROOT))
from representations import generate
from test_column_layouts import wrong_bit

@unittest.skipUnless(os.environ.get('INK_COMPILER'),'requires explicit compiler')
class ColumnPointTests(unittest.TestCase):
    def test_frozen_proposals_reproduce(self):
        d=ROOT/'research/column-points'
        with tempfile.TemporaryDirectory() as output:
            proposal=generate(json.loads((d/'model.json').read_text()),output,column_points=True)
        for name,request in zip(['direct','reversed'],proposal['requests']):
            self.assertEqual(request,json.loads((d/(name+'.json')).read_text()))

    def test_reauthenticated_wrong_comparison_is_rejected_mathematically(self):
        d=ROOT/'research/column-points'
        def corrupt(t):
            if isinstance(t,dict):
                x=t.get('If',{});b=x.get('condition',{}).get('Binary',{})
                if b.get('left')=={'Var':'column_query_key'} and b.get('op')=='==':
                    b['right']={'Var':'column_query_key'};return True
                return any(corrupt(v)for v in t.values())
            if isinstance(t,list):return any(corrupt(v)for v in t)
            return False
        with tempfile.TemporaryDirectory() as output:
            request=wrong_bit(json.loads((d/'direct.json').read_text()),Path(output)/'store',corrupt)
            path=Path(output)/'forged.json';path.write_text(json.dumps(request))
            result=subprocess.run([os.environ['INK_COMPILER'],'check-representation',d/'source.ink',path],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('definitional computation does not prove equality',result.stderr)

    def test_direct_search_composes_with_checked_boolean_word_fields(self):
        d=ROOT/'research/column-points'
        with tempfile.TemporaryDirectory() as output:
            proposal=generate(json.loads((d/'model.json').read_text()),str(Path(output)/'store'),column_points=True,packed_booleans=True)
            for i,request in enumerate(proposal['requests']):
                path=Path(output)/(str(i)+'.json');path.write_text(json.dumps(request))
                result=subprocess.run([os.environ['INK_COMPILER'],'check-representation',d/'source.ink',path],capture_output=True,text=True)
                self.assertEqual(result.returncode,0,result.stderr)
if __name__=='__main__':unittest.main()
