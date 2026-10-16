"""Guarded full-U32 remainder, strict operands and genuinely lazy fallback."""
import copy,json,os,random,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from producers.frozen_laws import specialize
from producers.v8_integer_laws import guarded_templates
from ink_planner.semantic_search import positions,match
ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'knowledge/producers/data/v8-integer-laws'
SOURCE=Path(__file__).parent/'fixtures/v8-variable-power/source.ink'
class VariablePower(unittest.TestCase):
 def test_discovery_source_full_width_strictness_laziness_and_false_support(self):
  compiler=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp)
   def run(*a,ok=True):
    r=subprocess.run([str(compiler),*map(str,a)],capture_output=True,text=True,timeout=180)
    if ok:self.assertEqual(r.returncode,0,r.stderr[-3000:])
    return r
   run('emit-core',SOURCE,'-o',d/'core.json');run('emit-semantic',d/'core.json','--core','-o',d/'subject.json');subject=json.loads((d/'subject.json').read_bytes())
   # The root pattern is independent of source function and operand names.
   rows=specialize(subject,DATA,'v8-integer/');law=next(l for n,l in rows if n=='v8-integer/u32_rem_or_variable_power_guard')
   self.assertEqual({k:law[k]for k in ['params','conditions','from','to']},guarded_templates()[0]['goal'])
   objects={identity(semantic_entry(l)):semantic_entry(l)for _,l in rows};rid=identity(semantic_entry(law));store=Store.publish(d/'source',[]);views=ProposalViews(store,objects,d/'transport');apps=[]
   for function in ['samples','strict_x','strict_y','lazy_default']:
    found=[]
    for path,target in positions(subject['functions'][function]):
     args={}
     if match(law['from'],target,law['params'],args):found.append(dict(function=function,path=list(path),law=rid,arguments=args,premises=[]))
    self.assertEqual(len(found),1,function);apps+=found
   selection=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=views.bundle([rid]),applications=apps);raw=canonical(selection);self.assertLess(len(raw),16_000_000);(d/'selection.json').write_bytes(raw);run('check-selection',d/'core.json',d/'selection.json')
   def call(function,args,budget=100000,selected=False):
    (d/'args.json').write_bytes(canonical(args));return run('run',d/'core.json',function,d/'args.json','--core','--evaluation-budget',budget,*(['--selection',d/'selection.json']if selected else []),ok=False)
   rng=random.Random(0x7638706f77);divisors=[0,*[1<<k for k in range(32)],3,5,7,9,0x7fffffff,0x80000001,0xffffffff]
   inputs=[dict(x=x,y=y,default=0xf1234567)for y in divisors for x in [0,1,0x7fffffff,0x80000000,0xffffffff,rng.getrandbits(32)]]
   expected=[r['x']%r['y']if r['y']else r['default']for r in inputs]
   for selected in [False,True]:
    r=call('samples',[inputs],1000000,selected);self.assertEqual(r.returncode,0,r.stderr[-2000:]);self.assertEqual(json.loads(r.stdout),expected)
    for function in ['strict_x','strict_y']:self.assertNotEqual(call(function,[0xf1234567,8],500,selected).returncode,0)
    self.assertEqual(json.loads(call('lazy_default',[0xf1234567,8],500,selected).stdout),7)
    self.assertEqual(json.loads(call('lazy_default',[0xf1234567,3],500,selected).stdout),0xf1234567%3)
    self.assertNotEqual(call('lazy_default',[0xf1234567,0],500,selected).returncode,0)
   # Authenticate a genuinely false constant dependency as a fresh root:
   # neither membership nor the original certificate admits it.
   support=copy.deepcopy(next(l for n,l in rows if l['from']['node'].get('Op',[None])[0]=='call:rem_or'and not l['params'].get('y')))
   support['to']=support['from']['node']['Op'][1][0];bad=semantic_entry(support);all_objects=dict(objects);all_objects[identity(bad)]=bad
   bad_view=ProposalViews(store,all_objects,d/'bad-transport').bundle([identity(bad)]);(d/'bad.json').write_bytes(canonical(bad_view));self.assertNotEqual(run('knowledge-check',d/'core.json',d/'bad.json',ok=False).returncode,0)
if __name__=='__main__':unittest.main()
