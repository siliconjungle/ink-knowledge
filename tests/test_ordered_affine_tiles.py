"""Replay the universal construction, reject altered order, and discover normally."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.ordered_affine_tiles import author,specialize

class OrderedAffineTiles(unittest.TestCase):
 def test_dimensions_and_checked_construction(self):
  compiler=Path(os.environ.get('INK_COMPILER',Path(__file__).resolve().parents[2]/'target/debug/ink')).resolve()
  for dims in [(0,1),(1,0),(1,17),(4294967295,2),(True,1)]:
   with self.assertRaises(ValueError):author(*dims)
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);source=d/'source.ink';core=d/'core.json';subject=d/'subject.json'
   source.write_text('module Independent;fn recurrence(values:List<u32>,initial:u32,factor:u32)->u32{return foldr(values,initial,fn(item)=>fn(state)=>item+state*factor);}fn nonlinear(values:List<u32>,initial:u32)->u32{return foldr(values,initial,fn(item)=>fn(state)=>item+state*state);}')
   def run(*args):
    p=subprocess.run([str(x)for x in [compiler,*args]],capture_output=True,text=True,timeout=180)
    self.assertEqual(p.returncode,0,p.stderr);return p
   run('emit-core',source,'-o',core);run('emit-semantic',core,'--core','-o',subject)
   for width,count in [(1,1),(3,2),(17,4),(4096,16)]:
    objects,names,root=author(width,count);store=Store.publish(d/f'store-{count}',objects.values(),{'root':root});view=d/'view.json';view.write_bytes(canonical(store.bundle([root])))
    run('knowledge-check',core,view)
   semantic=json.loads(subject.read_text());rows=specialize(semantic,json.loads(core.read_text()))
   self.assertTrue(rows)
   self.assertEqual(specialize({'functions':{'nonlinear':semantic['functions']['nonlinear']}},{}),[])
   # Rehashing a corrupted target cannot make the old proof establish it.
   altered=copy.deepcopy(objects[root]);altered['payload']['to']=altered['payload']['from']['node']['Op'][1][1]
   objects[identity(altered)]=altered
   store=Store.publish(d/'tampered',objects.values());view.write_bytes(canonical(store.bundle([identity(altered)])))
   p=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],capture_output=True,text=True,timeout=180)
   self.assertNotEqual(p.returncode,0,p.stdout)
   # Round-trip proposal authoring keeps every dependency's identity intact.
   self.assertEqual({identity(semantic_entry(row))for _,row in rows},set(author()[0]))

if __name__=='__main__':unittest.main()
