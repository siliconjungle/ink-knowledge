"""Narrow loop state requires transition and stopping equality on embedded states."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry

class UntilEmbedding(unittest.TestCase):
 def test_cannot_drop_simulation_or_change_iteration(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  directory=root/'knowledge/libraries/proofs/until-embedding';store=Store(directory)
  key=json.loads((directory/'store/names.json').read_text())['until_embedding'];original=store.object(key)
  objects=store.bundle([key])['objects']
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary)
   for label,change in [('complete',None),('missing-transition',lambda t:t['assumptions'].pop(0)),('missing-stop',lambda t:t['assumptions'].pop(1)),('changed-count',None)]:
    theorem=dict(copy.deepcopy(original['payload']),schema=1,semantics=original['semantics'],dependencies=original['dependencies'])
    if label=='changed-count':
     # The right endpoint is embed(until(...)); one extra iteration is unsound.
     from producers.semantic_laws import op,value,word
     args=theorem['to']['node']['Op'][1][1]['node']['Op'][1]
     args[0]=op(value('U32'),'binary:+',args[0],word('U32',1))
    elif change:change(theorem)
    obj=semantic_entry(theorem);entries=dict(objects);entries[identity(obj)]=obj
    trial=Store.publish(d/label,list(entries.values()));view=d/(label+'.json');view.write_bytes(canonical(trial.bundle([identity(obj)])))
    result=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120)
    self.assertEqual(result.returncode==0,label=='complete',label+' '+result.stderr[-2000:])

if __name__=='__main__':unittest.main()
