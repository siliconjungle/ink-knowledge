"""Nested mutable loop state narrowing must preserve types and branch premises."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry

class GuardedLoopEmbedding(unittest.TestCase):
 def test_leaf_specialization_requires_its_guard(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  directory=root/'knowledge/libraries/proofs/leaf-indexed-sequence';store=Store(directory);names=json.loads((directory/'store/names.json').read_text());objects=store.bundle([names['guarded_loop_embedding']])['objects']
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary)
   for label in ['complete','missing-leaf-premise','opposite-leaf-premise']:
    entries=dict(objects);roots=[names['guarded_loop_embedding']]
    if label!='complete':
     original=store.object(names['branch_true']);law=dict(copy.deepcopy(original['payload']),schema=1,semantics=original['semantics'],dependencies=original['dependencies'])
     if label=='missing-leaf-premise':law['conditions']=[]
     else:law['conditions'][0]['to']['node']['Bool']=False
     obj=semantic_entry(law);entries[identity(obj)]=obj;roots=[identity(obj)]
    trial=Store.publish(d/label,list(entries.values()));view=d/(label+'.json');view.write_bytes(canonical(trial.bundle(roots)))
    result=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120)
    self.assertEqual(result.returncode==0,label=='complete',label+' '+result.stderr[-2000:])

if __name__=='__main__':unittest.main()
