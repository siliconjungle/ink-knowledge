"""Direct column updates and shared maintenance require mathematical admission."""
import json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'producers'))
sys.path.insert(0,str(ROOT))
from representations import generate
from representation_product import generate as product
from test_column_layouts import wrong_bit

@unittest.skipUnless(os.environ.get('INK_COMPILER'),'requires explicit compiler')
class MutationTests(unittest.TestCase):
    def check(self,source,request,output):
        path=Path(output)/'check.json';path.write_text(json.dumps(request))
        return subprocess.run([os.environ['INK_COMPILER'],'check-representation',source,path],capture_output=True,text=True)
    def test_both_layouts_and_bit_columns_are_admitted(self):
        d=ROOT/'research/column-points'
        with tempfile.TemporaryDirectory()as output:
            proposals=generate(json.loads((d/'model.json').read_text()),Path(output)/'store',column_mutations=True,packed_booleans=True)
            for request in proposals['requests']:
                result=self.check(d/'source.ink',request,output)
                self.assertEqual(result.returncode,0,result.stderr)
    def test_reauthenticated_wrong_mutation_is_rejected(self):
        d=ROOT/'research/column-points'
        def corrupt(t):
            if isinstance(t,dict):
                x=t.get('If',{});b=x.get('condition',{}).get('Binary',{})
                if b.get('right')=={'Var':'head_key'} and b.get('left')=={'Var':'key'}:
                    b['right']={'U64':0};return True
                return any(corrupt(v)for v in t.values())
            if isinstance(t,list):return any(corrupt(v)for v in t)
            return False
        with tempfile.TemporaryDirectory()as output:
            request=generate(json.loads((d/'model.json').read_text()),Path(output)/'store',column_mutations=True)['requests'][0]
            forged=wrong_bit(request,Path(output)/'forged',corrupt)
            result=self.check(d/'source.ink',forged,output)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('definitional computation does not prove equality',result.stderr)
    def test_shared_product_is_admitted(self):
        d=ROOT/'research/product-caches'
        with tempfile.TemporaryDirectory()as output:
            read=lambda n:json.loads((d/(n+'.json')).read_text())
            request=product(read('model'),[read('zero'),read('one')],Path(output)/'store',{'one':1},True)
            result=self.check(d/'source.ink',request,output)
            self.assertEqual(result.returncode,0,result.stderr)
if __name__=='__main__':unittest.main()
