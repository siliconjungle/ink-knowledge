"""Concrete checked query/split equations cannot lose their applicability."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import op,value,word,var

class SelectionQueryReuse(unittest.TestCase):
 def test_replay_rejects_changed_position_and_missing_zero_premise(self):
  root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
  path=Path(os.environ.get('INK_QUERY_REUSE_STORE',root/'knowledge/libraries/proofs/selection-query-reuse'));source=path/'checked-source.json';store=Store(path)
  names=json.loads((path/'store/names.json').read_text());objects=store.bundle(list(names.values()))['objects']
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary)
   def check(label,entries,roots):
    published=Store.publish(d/label,list(entries.values()));view=d/(label+'.json');view.write_bytes(canonical(published.bundle(roots)))
    return subprocess.run([compiler,'knowledge-check',source,view],capture_output=True,text=True,timeout=120)
   r=check('valid',objects,list(names.values()));self.assertEqual(r.returncode,0,r.stderr[-2000:])
   def changed(label,key,modify):
    old=store.object(key);law=dict(copy.deepcopy(old['payload']),schema=1,semantics=old['semantics'],dependencies=old['dependencies']);modify(law)
    obj=semantic_entry(law);entries=dict(objects);entries[identity(obj)]=obj;r=check(label,entries,[identity(obj)])
    self.assertNotEqual(r.returncode,0,r.stdout)
   def wrong_position(law):
    args=law['to']['node']['Op'][1];args[1]=op(value('U32'),'binary:+',args[1],word('U32',1))
   changed('different-position',names['query_reuse'],wrong_position)
   changed('missing-zero',names['zero_argument'],lambda law:law.update(conditions=[]))
   changed('wrong-zero',names['zero_argument'],lambda law:law['conditions'][0].update(to=word('U32',1)))

if __name__=='__main__':unittest.main()
