"""Guarded choice reductions: proof, deployment and values."""
import copy,hashlib,json,os,random,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import word
from producers.web_guard22_laws import named_laws,scalar_laws,old_composition_laws,publish,source_functions,specialize
ROOT=Path(__file__).resolve().parents[1]
COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs'
PIN='edd38a3302391d76195c377189a95c4f9f893c497198b2c599ce6002df906d37'
COST=ROOT.parent/'reports/web-stack-proofs-21-2026-10-11/cpu-cost-model.json'


def alpha(law):
 names={}
 def visit(v):
  if isinstance(v,dict):
   if set(v)=={'Free'}:
    n=v['Free'];names.setdefault(n,'v'+str(len(names)));return {'Free':names[n]}
   return {k:visit(v[k]) for k in sorted(v)}
  if isinstance(v,list):return [visit(x) for x in v]
  return v
 return canonical(visit([law['from'],law['to'],law.get('conditions',[])]))


def wrap(v,t):
 bits=64 if t=='u64' else 32;v&=(1<<bits)-1
 return v-(1<<32) if t=='i32' and v>=1<<31 else v


def quotient(a,b,z,t):
 if b==0 or (t=='i32' and a==-(1<<31) and b==-1):return z
 q=abs(a)//abs(b)
 if t=='i32' and (a<0)!=(b<0):q=-q
 return wrap(q,t)


def callbacks(args,t,heldout):
 _,seed,k=args;n=lambda v:wrap(v,t)
 if heldout:
  return (lambda x:quotient(n(n(x*k)+seed),seed,k,t)>k,lambda x:n(n(x-seed if x>seed else seed-x)*3),lambda x:quotient(n(x+seed),k,seed,t),lambda x:quotient(n(x*k),k,seed,t),lambda x:n(x+k))
 return (lambda x:quotient(n(x+seed),k,k,t)<seed,lambda x:quotient(n(n(x*k)+seed),seed,k,t),lambda x:n(n(k-x if x<k else x-k)+seed),lambda x:n(x+seed),lambda x:quotient(n(x+seed),k,seed,t))


def literal(args,t,heldout,family):
 # Original eager map computes two condition evaluations per element; each
 # choose executes only its selected arm. Addition/subtraction wraps first.
 xs,_,_=args;n=lambda v:wrap(v,t);p,f,g,h,j=callbacks(args,t,heldout);values=[]
 for x in xs:
  a=f(x) if p(x) else (g(x) if family=='choice' else 0)
  if family=='choice':b=h(x) if p(x) else j(x)
  else:b=g(x) if not p(x) else 0
  values.append(n(a-b if family=='subtract' else a+b))
 acc=0
 for v in values:acc=n(acc+v)
 return acc


def mathematical(args,t,heldout,family):
 # One predicate decision and unbounded accumulation, independently combining
 # the selected contribution rather than traversing two zero-armed expressions.
 xs,_,_=args;p,f,g,h,j=callbacks(args,t,heldout);total=0
 for x in xs:
  c=p(x)
  if family=='choice':v=f(x)+h(x) if c else g(x)+j(x)
  elif family=='subtract':v=f(x) if c else -g(x)
  else:v=f(x) if c else g(x)
  total+=v
 return wrap(total,t)


def frames(t):
 bits=64 if t=='u64' else 32;hi=(1<<31)-1 if t=='i32' else (1<<bits)-1;lo=-(1<<31) if t=='i32' else 0;w=lambda n:wrap(n,t);rng=random.Random(2121)
 values=[lo,0,1,2,7,8,63,hi]
 return [[[],7,3],[values,7,3],[values,0,0],[values,hi,hi],[values,lo,w(-1)],
  [[0,1,2,3],7,3],[[7,8,9],0,hi],[[lo,hi,w(-3),0,1],w(-3),w(-3)],
  [[w(rng.getrandbits(bits)) for _ in range(17)],7,3],[[w(rng.getrandbits(bits)) for _ in range(17)],w(-3),w(-3)]]


class Guard22Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];self.archive=os.environ.get('INK_GUARD22_EVIDENCE')
  if self.archive:self.directory=Path(self.archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
  else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-guard22-');self.directory=Path(self.tmp.name)
 def tearDown(self):
  if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def run_command(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def test_alpha_fresh_independent_callback_families(self):
  old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1588);rows=named_laws();ids={identity(semantic_entry(l)) for _,l in rows};self.assertEqual(len(ids),6);self.assertFalse(ids&set(old.members()));endpoints={alpha(l) for _,l in rows}
  for oid in old.members():
   p=old.object(oid)['payload']
   if isinstance(p.get('from'),dict) and 'node' in p['from']:self.assertNotIn(alpha(p),endpoints)
  self.assertTrue(all(('c' in l['params'] or {'xs','p','f','g'}<=set(l['params'])) and not l['dependencies'] and not l['conditions'] for _,l in rows));(self.directory/'novelty.json').write_text(json.dumps(dict(baseline_snapshot=PIN,baseline_entries=1588,names={n:identity(semantic_entry(l)) for n,l in rows},fresh_mechanisms=1,old_composed_mechanisms=2,pointwise_roots=3,deployment_roots=3),indent=2)+'\n')
 def test_typed_selection_replay_allocation_free_and_complete_values(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08');self.assertEqual(hashlib.sha256(COST.read_bytes()).hexdigest(),'9524fee019274e2a5fd57b5ed8ff570dc7b63525f324e9f654efc8f6da0c85ec')
  rows=source_functions()+source_functions(True);src=self.directory/'typed.ink';src.write_text('module Typed22;\n'+'\n'.join(text for _,text in rows)+'\n');core=src.with_suffix('.core.json');subject=src.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject);original=json.loads(subject.read_text());static=specialize(original);self.assertEqual(len(static),18);st=publish(self.directory/'isolated',static);self.assertEqual(len(st.members()),51);admission=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json');apps=[];searches=[]
  for heldout in (False,True):
   for t in ('u32','i32','u64'):
    group=source_functions(heldout,t);unit=self.directory/f'{t}-{int(heldout)}.ink';unit.write_text('module Unit22;\n'+'\n'.join(text for _,text in group)+'\n');uc=unit.with_suffix('.core.json');out=unit.with_suffix('.selection.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc);r=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',4096,'--compact-output','-o',out);search=json.loads(r.stdout);searches.append(search);self.assertFalse(search['exhausted']);selection=json.loads(out.read_text());self.assertEqual(len(selection['applications']),3);apps+=selection['applications'];self.run_command(COMPILER,'check-selection',uc,out)
  combined=self.directory/'combined.selection.json';combined.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=original['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');replay=self.run_command(COMPILER,'check-selection',core,combined);selected=self.directory/'selected.core.json';after_sem=self.directory/'selected.semantic.json';self.run_command(COMPILER,'emit-core',src,'--selection',combined,'-o',selected);self.run_command(COMPILER,'emit-semantic',selected,'--core','-o',after_sem);after=json.loads(after_sem.read_text())['functions'];records=[]
  for name,_ in rows:
   body=json.dumps(after[name]);self.assertEqual(body.count('call:foldr'),1);self.assertNotIn('method:map',body);self.assertNotIn('method:filter',body);self.assertNotIn('call:sum',body);heldout=name.endswith('_heldout');t=name.replace('_heldout','').rsplit('_',1)[1];family='choice' if 'same_choice' in name else 'subtract' if 'subtract' in name else 'add'
   for index,args in enumerate(frames(t)):
    path=self.directory/f'args-{t}-{index}.json';path.write_text(json.dumps(args)+'\n');staged=literal(args,t,heldout,family);reference=mathematical(args,t,heldout,family);before=json.loads(self.run_command(COMPILER,'run',src,name,path).stdout);current=json.loads(self.run_command(COMPILER,'run',selected,name,path,'--core').stdout);self.assertEqual(staged,reference);self.assertEqual(before,current);self.assertEqual(before,reference);records.append(dict(function=name,type=t,arguments=args,original=before,selected=current,mathematical_reference=reference))
  (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'static-witnesses.json').write_text(json.dumps([dict(name=n,law=l) for n,l in static],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(fresh_generic_roots=6,old_generic_compositions=12,prior_dependencies=15,mechanisms=3,typed_source_instances=18,isolated_entries=len(st.members()),fresh_cpu_applications=len(apps),frames=len(records),actual_interpreter_runs=2*len(records),allocation_free_selected_bodies=18,admission=json.loads(admission.stdout),replay=json.loads(replay.stdout),searches=searches),indent=2)+'\n')
 def test_hash_valid_false_generic_endpoints_reject(self):
  src=self.directory/'negative.ink';src.write_text('module Negative22;\n'+source_functions(t='u32')[0][1]+'\n');core=src.with_suffix('.core.json');self.run_command(COMPILER,'emit-core',src,'-o',core);failures=[]
  for family in ('guard_complement_add','guard_complement_subtract','guard_same_choice_add'):
   bad=copy.deepcopy(dict(scalar_laws())[family+'_u32']);bad['to']=word('U32',1);st=publish(self.directory/family,[(family+'_false',bad)]);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(family=family,content_id=identity(semantic_entry(bad)),stderr=r.stderr))
  (self.directory/'false-endpoints.json').write_text(json.dumps(failures,indent=2)+'\n')
 def test_source_bridge_checks_condition_correlation(self):
  original=source_functions(t='u32')[0][1]
  wrongcomplement=original.replace('(quot_or(x+seed,k,k)<seed)==false','quot_or(x+seed,k,k)<seed')
  choice=source_functions(t='u32')[2][1];wrongcondition=choice.rsplit('quot_or(x+seed,k,k)<seed',1);wrongcondition=wrongcondition[0]+'x>k'+wrongcondition[1]
  failures=[]
  for label,text in [('wrong-complement',wrongcomplement),('different-condition',wrongcondition)]:
   self.assertNotEqual(text,original if label=='wrong-complement' else choice);src=self.directory/(label+'.ink');src.write_text('module Wrong22;\n'+text+'\n');core=src.with_suffix('.core.json');subject=src.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject);rows=specialize(json.loads(subject.read_text()));self.assertEqual(len(rows),1);st=publish(self.directory/label,rows);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(label=label,content_id=identity(semantic_entry(rows[0][1])),stderr=r.stderr))
  (self.directory/'false-correlation.json').write_text(json.dumps(failures,indent=2)+'\n')

if __name__=='__main__':unittest.main()
