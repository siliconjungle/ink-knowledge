"""Freshly authenticated semantic corruption cannot authorize generic grouping."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from ink_knowledge.store import operations
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()
FIXTURE=Path(os.environ.get('INK_GENERAL_INDEXED_DATABASE',ROOT/'knowledge/research/general-indexed'))


def rehash(request,selected,bad,root):
 original=request['knowledge']['objects'];pending=dict(original);mapping={};rewritten={}
 def remap(t):
  if isinstance(t,str):
   if t in mapping:return mapping[t]
   if t.startswith('call:') and t[5:] in mapping:return 'call:'+mapping[t[5:]]
   return t
  if isinstance(t,list):return [remap(x) for x in t]
  if isinstance(t,dict):return {k:remap(x) for k,x in t.items()}
  return t
 while pending:
  ready=[i for i,o in pending.items() if not set(o['dependencies'])&pending.keys()]
  if not ready:raise ValueError('cyclic fixture')
  for i in ready:
   obj=remap(bad if i==selected else pending[i]);obj['dependencies']=sorted(set(obj['dependencies']))
   if obj['semantics']=='first-order-inductive-equality-v1':obj['interface']['operations']=operations(obj['payload'])
   ident=identity(obj);mapping[i]=ident;rewritten[ident]=obj;del pending[i]
 store=Store.publish(root,rewritten.values(),leaf_size=2)
 return {**request,'representation':mapping[request['representation']],'knowledge':store.bundle([mapping[request['representation']]])}

class GenericIndexed(unittest.TestCase):
 def test_grouped_second_key_events_and_summary_are_checked(self):
  request=json.loads((FIXTURE/'request.json').read_bytes());names=json.loads((FIXTURE/'names.json').read_bytes());objects=request['knowledge']['objects'];plan=objects[request['representation']]['payload']
  chosen=[(names['table-1/grouped/replace-replace/execute'],'second-key'),(plan['actions']['put']['execute'],'event'),(names['table-0/branch'],'summary')]
  for selected,kind in chosen:
   with self.subTest(kind=kind),tempfile.TemporaryDirectory() as tmp:
    bad=copy.deepcopy(objects[selected]);body=bad['payload']['declaration']['Function']['body']
    def change(t):
     if isinstance(t,list):return [change(x) for x in t]
     if not isinstance(t,dict):return t
     if t=={'Var':'group_second'} and kind=='second-key':return {'Var':'group_first'}
     if kind=='event' and 'Construct' in t and t['Construct']['datatype']==plan['actions']['put']['result']['Data'] and t['Construct']['constructor']==0:
      c=copy.deepcopy(t['Construct']);events=c['arguments'][4];data=events['Construct']['datatype'];c['arguments'][4]={'Construct':dict(datatype=data,constructor=0,arguments=[])};return {'Construct':c}
     return {k:change(v) for k,v in t.items()}
    if kind=='summary':
     tree=bad['payload']['declaration']['Function']['result']['Data'];summary=objects[tree]['payload']['declaration']['Datatype']['constructors'][2]['fields'][4]['Data'];fields=objects[summary]['payload']['declaration']['Datatype']['constructors'][0]['fields']
     body['Construct']['arguments'][4]={'Construct':dict(datatype=summary,constructor=0,arguments=[{'Bool':False} if s=='Bool' else {'U64':0} for s in fields])}
    else:bad['payload']['declaration']['Function']['body']=change(body)
    self.assertNotEqual(bad,objects[selected])
    forged=rehash(request,selected,bad,Path(tmp)/'database');path=Path(tmp)/'request.json';path.write_bytes(canonical(forged)+b'\n')
    result=subprocess.run([str(COMPILER),'check-representation',str(ROOT/'examples/general-indexed.ink'),str(path)],capture_output=True,text=True,timeout=600)
    self.assertNotEqual(result.returncode,0)
    for incidental in ['hash mismatch','membership','undeclared','source-definition index mismatch']:self.assertNotIn(incidental,result.stderr)
    self.assertRegex(result.stderr,r'theorem|definitional computation does not prove equality')

if __name__=='__main__':unittest.main()
