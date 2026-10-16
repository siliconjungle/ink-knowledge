"""Ordinary source-bound unfolding preserves the complete strict call interface."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.inline_laws import specialize

ROOT=Path(__file__).resolve().parents[2]
SOURCE=Path(__file__).parent/'fixtures/strict-inlining/source.ink'
FUNCTIONS=dict(strict='mix',tail='reversed',nested='twice',untouched='copy',lazy='first',converted='conversion')
def compiler():return Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()
def run(*args,ok=True):
 r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=120)
 if ok and r.returncode:raise AssertionError(r.stderr[-4000:])
 return r

def packet(directory):
 from ink_planner.semantic_search import match,positions
 d=Path(directory);d.mkdir(parents=True,exist_ok=True)
 run(compiler(),'emit-core',SOURCE,'-o',d/'core.json')
 run(compiler(),'emit-semantic',d/'core.json','--core','-o',d/'semantic.json')
 core=json.loads((d/'core.json').read_bytes());subject=json.loads((d/'semantic.json').read_bytes())
 rows={label[7:]:law for label,law in specialize(subject,core)}
 objects={name:semantic_entry(rows[name])for name in set(FUNCTIONS.values())}
 store=Store.publish(d/'knowledge',objects.values());apps=[]
 for function,name in FUNCTIONS.items():
  law=rows[name]
  for path,target in positions(subject['functions'][function]):
   arguments={}
   if match(law['from'],target,law['params'],arguments):
    apps.append(dict(function=function,path=list(path),law=identity(objects[name]),arguments=arguments,premises=[]));break
  else:raise AssertionError('no call '+function)
 result=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=store.bundle(sorted(identity(o)for o in objects.values())),applications=apps)
 (d/'selection.json').write_bytes(canonical(result));run(compiler(),'check-selection',d/'core.json',d/'selection.json')
 return result,rows,core,subject

class StrictInlining(unittest.TestCase):
 def test_source_bound_applications_and_every_typed_argument_binding(self):
  with tempfile.TemporaryDirectory()as tmp:
   packet_,rows,core,subject=packet(tmp);self.assertEqual(len(packet_['applications']),6)
   # All formals become strict applications in declaration order; this includes
   # unused List/F32 inputs and U64 arguments missing from the old whitelist.
   for name,law in rows.items():
    params=[n for n,_ in next(f for f in core['program']['functions']if f['name']==name)['params']]
    target=law['to'];seen=[]
    while isinstance(target['node'],dict)and target['node'].get('Op',[''])[0]=='apply':
     target,arg=target['node']['Op'][1];seen.append(arg['node']['Free'])
    self.assertEqual(list(reversed(seen)),params,name)

 def test_unused_argument_work_and_lazy_branch_positions_are_preserved(self):
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);packet(d)
   def call(function,args,budget,selected):
    p=d/'args.json';p.write_bytes(canonical(args))
    return run(compiler(),'run',d/'core.json',function,p,'--core','--evaluation-budget',budget,*(['--selection',d/'selection.json']if selected else []),ok=False)
   for selected in [False,True]:
    for gate in [False,True]:
     r=call('strict',[17,gate],100,selected);self.assertNotEqual(r.returncode,0);self.assertIn('budget',r.stderr)
     r=call('strict',[17,gate],100000,selected);self.assertEqual(r.returncode,0,r.stderr);self.assertEqual(json.loads(r.stdout),43 if gate else 0)
    r=call('lazy',[17,False],100,selected);self.assertEqual(r.returncode,0,r.stderr);self.assertEqual(json.loads(r.stdout),0)
    r=call('lazy',[17,True],100,selected);self.assertNotEqual(r.returncode,0);self.assertIn('budget',r.stderr)

 def test_changed_source_definition_or_transplanted_binder_scope_rejects(self):
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);p,_,_,_=packet(d)
   source=d/'changed.ink';source.write_text(SOURCE.read_text().replace('first+first+','first+first+first+'))
   run(compiler(),'emit-core',source,'-o',d/'changed.json')
   run(compiler(),'emit-semantic',d/'changed.json','--core','-o',d/'changed-semantic.json')
   forged=copy.deepcopy(p);forged['input_core_sha256']=json.loads((d/'changed-semantic.json').read_bytes())['input_core_sha256']
   (d/'rebound.json').write_bytes(canonical(forged))
   r=run(compiler(),'check-selection',d/'changed.json',d/'rebound.json',ok=False);self.assertNotEqual(r.returncode,0)
   bad=copy.deepcopy(p);nested=next(a for a in bad['applications']if a['function']=='nested')
   changed=[]
   def escape(t):
    if isinstance(t,dict):
     if 'Bound'in t:t['Bound']+=1;changed.append(True)
     else:
      for v in t.values():escape(v)
    elif isinstance(t,list):
     for v in t:escape(v)
   escape(nested['arguments']);self.assertTrue(changed)
   (d/'transplant.json').write_bytes(canonical(bad));r=run(compiler(),'check-selection',d/'core.json',d/'transplant.json',ok=False);self.assertNotEqual(r.returncode,0)

if __name__=='__main__':
 import sys
 if len(sys.argv)==2:packet(Path(sys.argv[1]))
 else:unittest.main()
