"""Frozen dependency metadata transports checked witnesses, never authority."""
import copy
import gzip
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers import frozen_laws as frozen
from producers.semantic_laws import law,value,var,op,word
from tests.test_v8_integer_laws import compiler,run


class FrozenDependencies(unittest.TestCase):
 def examples(self):
  x=var(value('U32'),'x');zero=word('U32',0)
  add=lambda a:op(value('U32'),'binary:+',a,zero)
  support=law({'x':value('U32')},add(x),x)
  ident=identity(semantic_entry(support))
  use=lambda a:{'Use':dict(law=ident,arguments={'x':a},premises=[])}
  root=law({'x':value('U32')},add(add(x)),x,
           {'Trans':dict(middle=add(x),left=use(add(x)),right=use(x))},dependencies=[ident])
  return support,root

 def test_only_needed_support_is_loaded_first_and_partial_updates_preserve_it(self):
  support,root=self.examples();unrelated=law({},word('U32',7),word('U32',7))
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);frozen.update(d,[dict(name='root',law=root)],dependencies=[support,unrelated])
   packet=json.loads((d/'index.json').read_bytes());self.assertEqual(packet['schema'],2)
   seen=[];original=frozen._load_proof
   def load(directory,digest):seen.append(digest);return original(directory,digest)
   subject=dict(functions={'renamed':root['from']})
   with patch.object(frozen,'_load_proof',side_effect=load):rows=frozen.specialize(subject,d,'prefix/')
   self.assertEqual([w for _,w in rows],[support,root]);self.assertEqual(len(seen),2)
   self.assertNotIn(identity(unrelated),seen)
   self.assertEqual(frozen.update(d,[]),1)
   self.assertEqual(json.loads((d/'index.json').read_bytes())['objects'],packet['objects'])
   self.assertEqual(frozen.closure(d,rows),rows)
   self.assertEqual(frozen.specialize({'functions':{}},d,'prefix/'),[])
   with self.assertRaisesRegex(ValueError,'closure budget'):frozen.closure(d,[('root',root)],maximum_entries=1)
   for bound in [0,True,1025]:
    with self.assertRaisesRegex(ValueError,'closure bound'):frozen.closure(d,[('root',root)],maximum_entries=bound)

 def test_missing_remapped_and_corrupted_dependency_bytes_decline(self):
  support,root=self.examples();ident=identity(semantic_entry(support))
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);frozen.update(d,[dict(name='root',law=root)],dependencies=[support])
   packet=json.loads((d/'index.json').read_bytes())
   for mode in ['missing','wrong-file','path','corrupt']:
    current=copy.deepcopy(packet)
    if mode=='missing':current['objects']={}
    elif mode=='wrong-file':current['objects'][ident]=identity(root)
    elif mode=='path':current['objects'][ident]='../'+'a'*61
    else:(d/(identity(support)+'.json.gz')).write_bytes(gzip.compress(b'{}'))
    (d/'index.json').write_bytes(canonical(current))
    with self.assertRaises(ValueError):frozen.closure(d,[('root',root)])

 def test_authenticated_false_support_still_rejects_in_ordinary_checker(self):
  support,root=self.examples()
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);source=d/'source.ink';source.write_text('module dependencies; fn id(x:u32)->u32{return x;}')
   run(compiler(),'emit-core',source,'-o',d/'core.json')
   for mode in ['valid','false']:
    s=copy.deepcopy(support);r=copy.deepcopy(root)
    if mode=='false':
     s['proof']='Normalize';s['from']=word('U32',0);s['to']=word('U32',1)
     new_id=identity(semantic_entry(s));old_id=r['dependencies'][0]
     def replace(v):
      if isinstance(v,dict):return {k:replace(x)for k,x in v.items()}
      if isinstance(v,list):return [replace(x)for x in v]
      return new_id if v==old_id else v
     r=replace(r)
    library=d/mode;frozen.update(library,[dict(name='root',law=r)],dependencies=[s])
    rows=frozen.closure(library,[('root',r)]);objects=[semantic_entry(w)for _,w in rows]
    store=Store.publish(d/(mode+'-store'),objects);view=d/(mode+'.json');view.write_bytes(canonical(store.bundle([identity(semantic_entry(r))])))
    result=run(compiler(),'knowledge-check',d/'core.json',view,ok=False)
    self.assertEqual(result.returncode==0,mode=='valid',result.stderr)

 def test_dependencies_precede_consumers_when_definition_context_changes_ids(self):
  from ink_knowledge import proposals
  x=var(value('U32'),'x');call=lambda a:op(value('U32'),'call:adjust',a)
  support=law({'x':value('U32')},call(x),x)
  ident=identity(semantic_entry(support));use=lambda a:{'Use':dict(law=ident,arguments={'x':a},premises=[])}
  root=law({'x':value('U32')},call(call(x)),x,{'Trans':dict(middle=call(x),left=use(call(x)),right=use(x))},dependencies=[ident])
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);source=d/'source.ink';source.write_text('module context_dependencies; fn adjust(x:u32)->u32{return x+0;} pub fn probe(x:u32)->u32{return adjust(adjust(x));}')
   run(compiler(),'emit-core',source,'-o',d/'core.json');run(compiler(),'emit-semantic',d/'core.json','--core','-o',d/'subject.json')
   core=json.loads((d/'core.json').read_bytes());subject=json.loads((d/'subject.json').read_bytes())
   frozen.update(d/'library',[dict(name='root',law=root)],dependencies=[support])
   module=SimpleNamespace(__file__=__file__,specialize=lambda s,c:frozen.specialize(s,d/'library','test/'))
   with patch.object(proposals,'modules',return_value=(['producers.example'],[])),patch.object(proposals.importlib,'import_module',return_value=module):objects,receipts=proposals.generate(subject,core)
   self.assertEqual(receipts[0]['retargeted'],2);self.assertEqual(receipts[0]['rejected'],[])
   store=Store.publish(d/'store',objects.values());view=d/'view.json';view.write_bytes(canonical(store.bundle(list(objects))))
   run(compiler(),'knowledge-check',d/'core.json',view)
   self.assertNotIn(ident,objects)
   root_obj=next(o for o in objects.values()if o['dependencies'])
   self.assertTrue(all(i in objects for i in root_obj['dependencies']))


if __name__=='__main__':unittest.main()
