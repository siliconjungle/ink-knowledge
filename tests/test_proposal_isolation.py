"""Oversized discovery data must not suppress unrelated checkable proposals."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from ink_knowledge import Store,canonical,identity,proposals
from producers.semantic_laws import law,value,var,binary,word

class ProposalIsolation(unittest.TestCase):
 def generated(self,rows):
  producer=SimpleNamespace(__file__=__file__,specialize=lambda subject,core:rows)
  with patch.object(proposals,'modules',return_value=(['producers.trial'],[])),patch.object(proposals.importlib,'import_module',return_value=producer):
   return proposals.generate({'functions':{}},{'program':{'functions':[],'records':{},'enums':{}}})

 def test_oversized_proof_keeps_other_objects_and_does_not_admit_false_equations(self):
  sort=value('U32');x=var(sort,'x');good=law({'x':sort},binary('+',x,word('U32',0)),x)
  huge=copy.deepcopy(good)
  for _ in range(140):huge['proof']={'Sym':huge['proof']}
  wrong=law({'x':sort},binary('+',x,word('U32',1)),x)
  objects,receipts=self.generated([('oversized',huge),('good',good),('wrong',wrong)])
  self.assertEqual(len(objects),2);self.assertEqual(receipts[0]['candidates'],3)
  self.assertEqual(receipts[0]['rejected'],[dict(label='oversized',reason='canonical object nesting limit')])
  from ink_knowledge.store import semantic_entry
  gid=identity(semantic_entry(good));wid=identity(semantic_entry(wrong));self.assertEqual(set(objects),{gid,wid})
  # Discovery creates data only. The independent checker must still reject the
  # false equation, even though its canonical object was structurally valid.
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  with tempfile.TemporaryDirectory()as td:
   d=Path(td);source=d/'source.ink';source.write_text('module trial;fn id(x:u32)->u32{return x;}');core=d/'core.json'
   emitted=subprocess.run([compiler,'emit-core',source,'-o',core],capture_output=True,text=True,timeout=180);self.assertEqual(emitted.returncode,0,emitted.stderr)
   store=Store.publish(d/'knowledge',list(objects.values()))
   for name,roots,accepted in [('good',[gid],True),('wrong',[wid],False)]:
    view=d/(name+'.json');view.write_bytes(canonical(store.bundle(roots)))
    result=subprocess.run([compiler,'knowledge-check',core,view],capture_output=True,text=True,timeout=180)
    self.assertEqual(result.returncode==0,accepted,name+' '+result.stderr[-1200:])
  # Rejected candidates remain deterministic when the producer returns them in
  # another order; the surviving content identities do not depend on order.
  again,_=self.generated([('wrong',wrong),('good',good),('oversized',huge)])
  self.assertEqual(set(again),set(objects))
if __name__=='__main__':unittest.main()
