"""Fresh authentication cannot excuse incorrect insertion or key ordering."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical
from producers.generic_indexed import generate
from test_generic_indexed import rehash,ROOT,COMPILER
class Extensions(unittest.TestCase):
 def test_insert_key_and_nominal_key_order_are_mathematically_checked(self):
  # Author the exact current source projection in a private store. Historical
  # receipts remain evidence; they cannot stand in for this admission.
  with tempfile.TemporaryDirectory() as directory:
   directory=Path(directory);model=directory/'model.json'
   subprocess.run([str(COMPILER),'emit-action-model',str(ROOT/'examples/indexed-key-types.ink'),'-o',str(model)],check=True,capture_output=True,text=True)
   generated=generate(json.loads(model.read_text()),directory/'database')
   current=generated['request'];entries=json.loads((directory/'database/store/names.json').read_text())
   packet=directory/'valid.json';packet.write_bytes(canonical(current)+b'\n')
   subprocess.run([str(COMPILER),'check-representation',str(ROOT/'examples/indexed-key-types.ink'),str(packet)],check=True,capture_output=True,text=True,timeout=600)
  for label,source,role,kind in [
   ('keys','indexed-key-types.ink','table-0/grouped/insert-insert/execute','second-key'),
   ('keys','indexed-key-types.ink','table-1/key_less','order')]:
   with self.subTest(kind=kind),tempfile.TemporaryDirectory() as tmp:
    request=copy.deepcopy(current)
    selected=entries[role];bad=copy.deepcopy(request['knowledge']['objects'][selected])
    def change(t):
     if isinstance(t,list):return [change(x) for x in t]
     if not isinstance(t,dict):return t
     if t=={'Var':'group_second'}:return {'Var':'group_first'}
     return {k:change(v) for k,v in t.items()}
    f=bad['payload']['declaration']['Function']
    f['body']={'Bool':False} if kind=='order' else change(f['body'])
    self.assertNotEqual(bad,request['knowledge']['objects'][selected])
    forged=rehash(request,selected,bad,Path(tmp)/'database');path=Path(tmp)/'request.json';path.write_bytes(canonical(forged)+b'\n')
    result=subprocess.run([str(COMPILER),'check-representation',str(ROOT/'examples'/source),str(path)],capture_output=True,text=True,timeout=600)
    self.assertNotEqual(result.returncode,0)
    for incidental in ['hash mismatch','membership','undeclared','source-definition index mismatch']:self.assertNotIn(incidental,result.stderr)
    self.assertRegex(result.stderr,r'theorem|definitional computation does not prove equality')
if __name__=='__main__':unittest.main()
