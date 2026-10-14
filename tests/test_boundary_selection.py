"""Complete guarded selection equality needs its exact guard and source result."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry

class BoundarySelection(unittest.TestCase):
 def test_complete_result_and_guard_cannot_be_changed(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  directory=root/'knowledge/libraries/proofs/boundary-selection';store=Store(directory);names=json.loads((directory/'store/names.json').read_text())
  key=names['boundary_selection_expression'];original=store.object(key);objects=store.bundle([key])['objects']
  # The exported equations must work without the proof-authoring observers.
  for obj in objects.values():
   definitions=obj.get('payload',{}).get('definition_context',{}).get('definitions',{})
   self.assertFalse({'selected_engine','split_zero'}&set(definitions))
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary)
   for label in ['complete','opposite-guard','different-result']:
    law=dict(copy.deepcopy(original['payload']),schema=1,semantics=original['semantics'],dependencies=original['dependencies'])
    if label=='opposite-guard':law['proof']['Cases']['condition']['node']['Op'][0]='binary:!='
    if label=='different-result':
     from producers.semantic_laws import op,value,word
     args=law['to']['node']['Op'][1][1]['node']['Op'][1]
     args[1]=op(value('U32'),'binary:+',args[1],word('U32',1))
    obj=semantic_entry(law);entries=dict(objects);entries[identity(obj)]=obj;trial=Store.publish(d/label,list(entries.values()));view=d/(label+'.json');view.write_bytes(canonical(trial.bundle([identity(obj)])))
    result=subprocess.run([compiler,'knowledge-check',directory/'checked-source.json',view],capture_output=True,text=True,timeout=120)
    self.assertEqual(result.returncode==0,label=='complete',label+' '+result.stderr[-2000:])

if __name__=='__main__':unittest.main()
