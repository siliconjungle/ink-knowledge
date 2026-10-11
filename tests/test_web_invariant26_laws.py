"""Checked invariant control hoisting: novelty, deployment and exact values."""
import copy,hashlib,json,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.web_invariant26_laws import named_laws,source_functions,specialize,publish,PIN
from producers.semantic_laws import bound,value
from knowledge.tests import test_web_accepted25_laws as previous
ROOT=Path(__file__).resolve().parents[1];COMPILER=ROOT.parent.parent/'toolchain/ink-accepted-proofs';COST=ROOT.parent/'reports/web-stack-proofs-25-2026-10-11/cpu-cost-model.json'

def frames(t):
 rows=previous.frames(t)
 # Both invariant directions are covered for every numeric type.
 rows += [[[0,1,2,3,7],1,8],[[0,1,2,3,7],8,1],[[0,1,2,3,7],7,7]]
 return rows

def oracle(name,args):
 t=name.rsplit('_',1)[1];n=lambda x:previous.norm(x,t);xs,seed,k=args;xs=[n(previous.number(x)) for x in xs];seed,k=n(previous.number(seed)),n(previous.number(k));yes=seed<k;held='heldout' in name
 if 'map' in name:
  def mapper(x):
   if held:return (n(n(x*k)-seed) if x>k else n(seed+x)) if yes else (n(x+seed) if x<k else n(x-k))
   return (n(seed-x) if x<seed else n(x+seed)) if yes else (n(x-seed) if x>seed else n(x*k))
  return [mapper(x) for x in xs]
 acc=seed
 for x in reversed(xs):
  if held:
   acc=(n(n(acc*k)+x) if x<seed else n(acc-x)) if yes else (n(n(x*k)+acc) if acc<k else n(x-n(acc*seed)))
  else:
   acc=(n(x+n(acc*k)) if acc<seed else n(x-acc)) if yes else (n(acc-n(x*seed)) if acc>k else n(acc+x))
 return acc

class Invariant26Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];archive=os.environ.get('INK_INVARIANT26_EVIDENCE')
  if archive:self.directory=Path(archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True);self.archive=True
  else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-invariant26-');self.directory=Path(self.tmp.name);self.archive=False
 def tearDown(self):
  if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 command=previous.Accepted25Tests.command
 compile=previous.Accepted25Tests.compile
 assert_value=previous.Accepted25Tests.assert_value
 def compile(self,name,text):
  src=self.directory/(name+'.ink');src.write_text('module Invariant26;\n'+text+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');self.command(COMPILER,'emit-core',src,'-o',core);self.command(COMPILER,'emit-semantic',core,'--core','-o',sem);return src,core,json.loads(sem.read_text())
 def test_novelty_and_every_prior_first_step(self):
  from producers.beta_sharing17 import derive
  from producers.web_algebra20_laws import named_laws as old_gates
  old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1758)
  proposed={previous.alpha(v) for _,v in named_laws()};self.assertEqual(len(proposed),8);generic=[]
  for i in sorted(old.members()):
   o=old.object(i);v=dict(o['payload'],schema=1,semantics=o['semantics'],dependencies=o['dependencies'])
   if all(k in v for k in ['params','from','to','proof']) and isinstance(v['from'],dict) and 'node' in v['from']:
    self.assertNotIn(previous.alpha(v),proposed);generic.append(('prior_'+i,v))
  duplicate_ids={n:identity(semantic_entry(v)) for n,v in old_gates() if n.startswith('gated_arbitrary_fold')}
  self.assertTrue(set(duplicate_ids.values())<=set(old.members()))
  records=[]
  for name,t,text in source_functions()+source_functions(True):
   if t!='u32':continue
   src,core,subject=self.compile(name,text);checks=[]
   for j,(label,v) in enumerate(derive(subject,generic)):
    objects=list(old.bundle(v['dependencies'])['objects'].values())+[semantic_entry(v)];st=Store.publish(self.directory/(name+'-old-'+str(j)),objects,{label:identity(semantic_entry(v))});view=st.root/'view.json';view.write_bytes(canonical(st.bundle([identity(semantic_entry(v))]))+b'\n');r=self.command(COMPILER,'knowledge-check',core,view,success=False);checks.append(dict(name=label,id=identity(semantic_entry(v)),exit_code=r.returncode,stderr=r.stderr,law=v))
   records.append(dict(function=name,proposals=checks,accepted=sum(c['exit_code']==0 for c in checks)))
  (self.directory/'old-opportunities.json').write_text(json.dumps(dict(prior_snapshot=PIN,prior_entries=1758,prior_semantic_laws=len(generic),excluded_exact_old_noop_fold=duplicate_ids,sources=records,scope='All historical semantic candidates offered; first-step only, not a complete mathematical nonderivability claim. Root full bounded frontier is offered symmetrically.'),indent=2)+'\n')
 def test_typed_admission_default_fold_selection_and_complete_values(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'3e358acc9026c1dbcc9ab2183a11e1d240b02196d0f3d8ecbb8740603b3c06a2')
  sources=source_functions()+source_functions(True);src,core,subject=self.compile('all','\n'.join(s for _,_,s in sources));certs=specialize(subject);self.assertEqual(len(certs),16);st=publish(self.directory/'isolated',certs);admit=self.command(COMPILER,'knowledge-check',core,st.root/'view.json')
  sel=self.directory/'default.selection.json';search=self.command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',512,'--compact-output','-o',sel);applications=json.loads(sel.read_text())['applications'];self.assertEqual({a['function'] for a in applications},{n for n,_,_ in sources if 'fold' in n});self.assertEqual(len(applications),8);self.command(COMPILER,'check-selection',core,sel)
  # Map certificates are valid but not chosen by this frozen model: reify explicitly, not a profitability claim.
  by_target={canonical(v['from']):identity(semantic_entry(v)) for _,v in certs};allapps=[dict(function=n,path=[],law=by_target[canonical(subject['functions'][n])],arguments={k:{'sort':s,'node':{'Free':k}} for k,s in next(v['params'] for _,v in certs if v['from']==subject['functions'][n]).items()},premises=[]) for n,_,_ in sources]
  whole=self.directory/'all.selection.json';whole.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=st.bundle([a['law'] for a in allapps]),applications=allapps),separators=(',',':'))+'\n');replay=self.command(COMPILER,'check-selection',core,whole);selected=self.directory/'selected.core.json';self.command(COMPILER,'emit-core',src,'--selection',whole,'-o',selected)
  records=[]
  for name,t,_ in sources:
   for i,args in enumerate(frames(t)):
    path=self.directory/f'args-{t}-{i}.json';path.write_text(json.dumps(args)+'\n');before=json.loads(self.command(COMPILER,'run',src,name,path).stdout);after=json.loads(self.command(COMPILER,'run',selected,name,path,'--core').stdout);self.assertEqual(before,after);self.assert_value(after,oracle(name,args),t);records.append(dict(function=name,type=t,arguments=args,gate=previous.number(args[1])<previous.number(args[2]),original=before,selected=after))
  (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v) for n,v in certs],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(generic_endpoints=8,typed_certificates=16,default_fold_applications=8,default_map_applications=0,typed_frames=len(records),interpreter_runs=len(records)*2,admission=json.loads(admit.stdout),replay=json.loads(replay.stdout),search=json.loads(search.stdout),gpu_builds=0,timing_calls=0),indent=2)+'\n')
 def test_hash_valid_false_controls_and_invariant_capture(self):
  src,core,_=self.compile('controls',source_functions()[0][2]);rules=dict(named_laws());bad=copy.deepcopy(rules['invariant_two_branch_fold_u32']);bad['to']['node']['Op'][1][1],bad['to']['node']['Op'][1][2]=bad['to']['node']['Op'][1][2],bad['to']['node']['Op'][1][1]
  badmap=copy.deepcopy(rules['invariant_two_branch_map_u32']);badmap['to']['node']['Op'][1][2]=copy.deepcopy(badmap['to']['node']['Op'][1][1]);fail=[]
  for name,v in [('swapped-live-reducers',bad),('wrong-false-mapper',badmap)]:
   st=publish(self.directory/name,[(name,v)]);r=self.command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);fail.append(dict(name=name,id=identity(semantic_entry(v)),stderr=r.stderr))
  _,_,varying=self.compile('varying','pub fn arbitrary(xs:List<u32>,seed:u32,k:u32)->u32{return foldr(xs,seed,fn(x)=>fn(a)=>choose(a<k,x+a,x-a));}')
  self.assertEqual(specialize(varying),[])
  _,_,varyingmap=self.compile('varying-map','pub fn arbitrary(xs:List<u32>,seed:u32,k:u32)->List<u32>{return xs.map(fn(x)=>choose(x<k,x+seed,x-seed));}')
  self.assertEqual(specialize(varyingmap),[])
  # Nested callback capture is accepted, while reducer-local gate was refused.
  _,_,nested=self.compile('capture','pub fn arbitrary(xs:List<u32>,seed:u32,k:u32)->List<u32>{return xs.map(fn(x)=>choose(seed<k,foldr(xs,x,fn(y)=>fn(a)=>choose(a<seed,x+a*k,y-a)),x-k));}')
  cert=specialize(nested);self.assertEqual(len(cert),1);st=publish(self.directory/'capture',cert);self.command(COMPILER,'knowledge-check',core,st.root/'view.json')
  (self.directory/'controls.json').write_text(json.dumps(dict(false_controls=fail,varying_accumulator_gate_unmatched=True,varying_element_gate_unmatched=True,nested_callback_capture_checked=True,counterexamples=dict(swapped_fold=dict(xs=[1],z=3,c=True,h='x+a',j='x-a',source=4,false_target=4294967294),wrong_map=dict(xs=[1],c=False,f='x+1',g='x+2',source=[3],false_target=[2]))),indent=2)+'\n')
if __name__=='__main__':unittest.main()
