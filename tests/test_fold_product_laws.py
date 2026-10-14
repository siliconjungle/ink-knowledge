"""Sharing a traversal requires independently updated product fields."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path

class FoldProductLaws(unittest.TestCase):
 def test_induction_rejects_cross_coupling_and_reordered_observations(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  source=(root/'knowledge/libraries/fold-product-laws.ink').read_text()
  variants=[('valid',source,True),('cross-coupled',source.replace('first(item,p.first)','first(item,p.second)'),False),('opposite-order',source.replace('first:foldl(xs,left,first)','first:foldr(xs,left,first)'),False)]
  with tempfile.TemporaryDirectory()as td:
   d=Path(td)
   for name,text,accepted in variants:
    path=d/(name+'.ink');path.write_text(text)
    result=subprocess.run([compiler,'emit-laws',path,'-o',d/(name+'.json')],capture_output=True,text=True,timeout=180)
    self.assertEqual(result.returncode==0,accepted,name+' '+result.stderr[-1500:])
    if accepted:self.assertEqual(set(json.loads(result.stdout)['names']),{'fold_product'})
if __name__=='__main__':unittest.main()
