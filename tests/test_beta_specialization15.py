"""Producer binding/budget regressions; admission tests use the frozen checker."""
import sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from producers.beta_specialization15 import beta_normalize,instantiate_bound,free_parameters
from producers.semantic_laws import arrow,bound,lam,op,value,var
class BetaSpecializationTests(unittest.TestCase):
    def test_nested_binder_preserves_local_and_shifts_argument(self):
        s=value('U32');body=lam(s,op(s,'binary:+',bound(s,0),bound(s,1)))
        self.assertEqual(instantiate_bound(body,bound(s,0)),lam(s,op(s,'binary:+',bound(s,0),bound(s,1))))
        x=var(s,'x');self.assertEqual(instantiate_bound(body,x),lam(s,op(s,'binary:+',bound(s,0),x)))
    def test_unknown_callback_is_preserved(self):
        s=value('U32');f=var(arrow(s,s),'f');x=var(s,'x');term=op(s,'apply',f,x)
        self.assertEqual(beta_normalize(term),term)
        self.assertEqual(free_parameters(term),{'f':arrow(s,s),'x':s})
    def test_budget_is_bounded_and_known_identity_reduces(self):
        s=value('U32');x=var(s,'x');term=op(s,'apply',lam(s,bound(s,0)),x)
        self.assertEqual(beta_normalize(term),x)
        with self.assertRaises(ValueError):beta_normalize(term,budget=1)
if __name__=='__main__':unittest.main()
