import tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,identity
from ink_knowledge.recipes import role
from producers.physical_capabilities import base
from producers.carrier_fusion import specialize
from producers.semantic_laws import value,var,op,lam,bound
class Capabilities(unittest.TestCase):
 def test_baseline_and_physical_choices_do_not_supply_proofs(self):
  p=base('a'*64);self.assertEqual(p['buffers'],'scoped');self.assertEqual(p['columns'],[]);self.assertNotIn('bounds',p)
  for sem in ['ink-source-read-capability-v1','ink-source-column-map-v1']:self.assertEqual(role(dict(kind='definition',semantics=sem)),'physical-proof-dependency')
 def test_cross_carrier_composition_is_proposed_with_induction_and_no_apply_holes(self):
  A=value({'Named':'Row'});B=value('U32');xs=var(value({'List':{'Named':'Row'}}),'xs');f=lam(A,op(B,'field:x',bound(A,0)));g=lam(B,op(B,'binary:+',bound(B,0),dict(sort=B,node={'Word':1})))
  source=op(value({'List':'U32'}),'method:map',op(value({'List':'U32'}),'method:map',xs,f),g);rows=specialize(dict(functions={'f':source}));self.assertEqual(len(rows),1);proposal=rows[0][1];self.assertIn('Induction',proposal['proof']);self.assertEqual(proposal['to']['node']['Op'][0],'method:map');self.assertNotIn('apply',str(proposal['to']))
 def test_captured_bindings_remain_free_parameters(self):
  A=value('U32');xs=var(value({'List':'U32'}),'xs');f=lam(A,op(A,'binary:+',bound(A,0),var(A,'offset')));source=op(xs['sort'],'method:map',op(xs['sort'],'method:map',xs,f),f);proposal=specialize(dict(functions={'f':source}))[0][1];self.assertIn('offset',proposal['params']);self.assertEqual(proposal['params']['offset'],A)
if __name__=='__main__':unittest.main()
