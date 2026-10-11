"""Freshly authenticated incorrect layouts and observations remain untrusted."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from producers.representations import refs
from ink_knowledge.store import operations
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
class IndexedAdmission(unittest.TestCase):
 def test_false_cached_sum_range_and_event_are_rejected_after_rehashing(self):
  request=json.loads((ROOT/'knowledge/research/indexed-aggregate/request.json').read_text())
  names=json.loads((ROOT/'knowledge/store/names.json').read_text())
  for name,kind in [('branch','sum'),('branch','range'),('observe_put','event')]:
   with self.subTest(kind=kind),tempfile.TemporaryDirectory() as tmp:
    selected=names['indexed-aggregate/'+name];original=request['knowledge']['objects'];self.assertIn(selected,original)
    bad=copy.deepcopy(original[selected]);body=bad['payload']['declaration']['Function']['body']
    if kind in ['sum','range']:body['Construct']['arguments'][4 if kind=='sum' else 2]={'U64':0}
    else:
     observation=bad['payload']['declaration']['Function']['result']['Data']
     events=original[observation]['payload']['declaration']['Datatype']['constructors'][0]['fields'][4]['Data']
     body['Match']['branches'][0]['body']['Construct']['arguments'][4]={'Construct':{'datatype':events,'constructor':0,'arguments':[]}}
    # Recompute every identity and reference. Hash/membership rejection would
    # not exercise the mathematical admission boundary.
    rewritten={};mapping={};pending=dict(original)
    def remap(t):
     if isinstance(t,str):
      if t in mapping:return mapping[t]
      if t.startswith('call:') and t[5:] in mapping:return 'call:'+mapping[t[5:]]
      return t
     if isinstance(t,list):return [remap(v) for v in t]
     if isinstance(t,dict):return {k:remap(v) for k,v in t.items()}
     return t
    while pending:
     ready=[i for i,o in pending.items() if not set(o['dependencies'])&pending.keys()]
     self.assertTrue(ready,'acyclic proposal')
     for i in ready:
      obj=remap(bad if i==selected else pending[i]);obj['interface']['operations']=operations(obj['payload']) if obj['semantics']=='first-order-inductive-equality-v1' else obj['interface']['operations']
      obj['dependencies']=sorted(set(obj['dependencies']));new=identity(obj);mapping[i]=new;rewritten[new]=obj;del pending[i]
    store=Store.publish(Path(tmp)/'database',rewritten.values(),leaf_size=2)
    forged={**request,'representation':mapping[request['representation']],'knowledge':store.bundle([mapping[request['representation']]])}
    path=Path(tmp)/'request.json';path.write_bytes(canonical(forged)+b'\n');self.assertLessEqual(path.stat().st_size,16_000_000)
    result=subprocess.run([str(COMPILER),'check-representation',str(ROOT/'examples/filtered-aggregate.ink'),str(path)],capture_output=True,text=True,timeout=300)
    self.assertNotEqual(result.returncode,0);self.assertNotIn('hash mismatch',result.stderr);self.assertNotIn('membership',result.stderr);self.assertNotIn('undeclared',result.stderr)
if __name__=='__main__':unittest.main()
