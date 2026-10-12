"""Fresh authentication cannot excuse incorrect insertion or key ordering."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical
from test_generic_indexed import rehash,ROOT,COMPILER
class Extensions(unittest.TestCase):
 def test_insert_key_and_nominal_key_order_are_mathematically_checked(self):
  fixtures=ROOT/'knowledge/research/indexed-extensions'
  for label,source,role,kind in [
   ('keys','indexed-key-types.ink','table-0/grouped/insert-insert/execute','second-key'),
   ('keys','indexed-key-types.ink','table-1/key_less','order')]:
   with self.subTest(kind=kind),tempfile.TemporaryDirectory() as tmp:
    receipt=json.loads((fixtures/(label+'.json')).read_bytes())
    store=Store(ROOT/'knowledge',ROOT/'knowledge/store/snapshots'/(receipt['view_snapshot']+'.json'))
    request=dict(schema=1,semantics='ink-source-representation-v1',input_core_sha256=receipt['source'],representation=receipt['representation'],knowledge=store.bundle([receipt['representation']]))
    selected=receipt['entries'][role];bad=copy.deepcopy(request['knowledge']['objects'][selected])
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
