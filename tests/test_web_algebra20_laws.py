"""Loop-invariant gate proofs, checked compositions and typed execution."""
import copy,hashlib,json,math,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import word
from producers.web_algebra20_laws import named_laws,publish,source_functions,specialize
from producers.web_collection14_laws import named_laws as prior_sum_laws

ROOT=Path(__file__).resolve().parents[1]
COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs'
PIN='6f99dae6d3ca740006f5840d179e17afcb43c5a99c34b5ffb1c02b73d207b177'
COST=ROOT.parent/'reports/web-stack-proofs-19-2026-10-11/cpu-cost-model.json'


def alpha(candidate):
 names={}
 def visit(v):
  if isinstance(v,dict):
   if set(v)=={'Free'}:
    name=v['Free'];names.setdefault(name,'v'+str(len(names)));return {'Free':names[name]}
   return {k:visit(v[k]) for k in sorted(v)}
  if isinstance(v,list):return [visit(x) for x in v]
  return v
 return canonical(visit([candidate['from'],candidate['to'],candidate.get('conditions',[])]))


def number(v):return struct.unpack('<f',struct.pack('<I',v['F32Bits']))[0] if isinstance(v,dict) else v


def normalize(v,t):
 if t=='f32':
  try:return struct.unpack('<f',struct.pack('<f',v))[0]
  except OverflowError:return math.copysign(math.inf,v)
 width=64 if t=='u64' else 32;v&=(1<<width)-1
 return v-(1<<32) if t=='i32' and v>=1<<31 else v


def reference(args,t,heldout,family,literal):
 xs,seed,k=args;xs=list(map(number,xs));seed,k=number(seed),number(k);n=lambda x:normalize(x,t)
 gate=seed==k if heldout else seed<k
 if family=='count':return sum((gate and (x>k if heldout else x<seed)) for x in xs)
 if family=='sum':
  def callback(x):
   if heldout:return n(n(seed-x if x<seed else x-seed)+k)
   a=n(x+seed)
   if k==0 or (t=='i32' and a==-(1<<31) and k==-1):return seed
   q=abs(a)//abs(k)
   if t=='i32' and (a<0)!=(k<0):q=-q
   return n(q)
  if literal:
   mapped=[callback(x) if gate else 0 for x in xs];a=0
   for x in mapped:a=n(a+x)
   return a
  return n(sum(callback(x) for x in xs)) if gate else 0
 a=seed
 if not gate:return a
 for x in reversed(xs):
  if heldout:
   if literal or t=='f32':a=n(a+n(x*seed)) if x<k else n(a-n(x*k))
   else:a=a+x*seed if x<k else a-x*k
  elif literal or t=='f32':a=n(n(x+seed)*n(a+k))
  else:a=(x+seed)*(a+k)
 return n(a)


def frames(t):
 rng=random.Random(2020)
 if t=='f32':
  special=[{'F32Bits':0x7fc00123},{'F32Bits':0x7f800000},{'F32Bits':0xff800000},0.0,-0.0]
  return [[[],2.0,3.0],[[],2.0,2.0],[[0.0,-0.0,1.0,2.0,3.0],2.0,3.0],
    [[0.0,-0.0,1.0,2.0,3.0],3.0,2.0],[special,2.0,2.0],[special,2.0,3.0],
    [[1.0,-1.0,2.0],{'F32Bits':0x7fc00123},2.0],
    [[1e20,-1e20,1.5,-2.0],-2.0,1e20],[[1e20,-1e20,1.5,-2.0],-2.0,-2.0],
    [[rng.randrange(-1000,1000)/8 for _ in range(11)],17.25,17.25]]
 width=64 if t=='u64' else 32;hi=(1<<31)-1 if t=='i32' else (1<<width)-1;lo=-(1<<31) if t=='i32' else 0
 xs=[0,1,7,8,63,127,hi,lo]
 return [[[],7,8],[[],7,7],[xs,7,8],[xs,8,7],[xs,7,7],[xs,0,0],
   [[hi,lo,hi,1,0],normalize(-3,t),normalize(-3,t)],
   [[lo,0,1,-1] if t=='i32' else [hi,0,1],0,normalize(-1,t)],
   [[normalize(rng.getrandbits(width),t) for _ in range(11)],7,8],
   [[normalize(rng.getrandbits(width),t) for _ in range(11)],normalize(-3,t),normalize(-3,t)]]


class Algebra20Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];self.archive=os.environ.get('INK_ALGEBRA20_EVIDENCE')
  if self.archive:self.directory=Path(self.archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
  else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-algebra20-');self.directory=Path(self.tmp.name)
 def tearDown(self):
  if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def run_command(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def test_alpha_fresh_generic_mechanisms(self):
  old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1343)
  rows=named_laws();ids={identity(semantic_entry(l)) for _,l in rows};self.assertEqual(len(ids),11);self.assertFalse(ids&set(old.members()))
  endpoints={alpha(l) for _,l in rows}
  for oid in old.members():
   p=old.object(oid)['payload']
   if isinstance(p.get('from'),dict) and 'node' in p['from']:self.assertNotIn(alpha(p),endpoints)
  self.assertTrue(all(not l['conditions'] and not l['dependencies'] for _,l in rows))
  (self.directory/'novelty.json').write_text(json.dumps(dict(baseline_snapshot=PIN,baseline_entries=1343,names={n:identity(semantic_entry(l)) for n,l in rows},mechanisms=3),indent=2)+'\n')
 def test_typed_admission_default_selection_replay_and_oracles(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
  self.assertEqual(hashlib.sha256(COST.read_bytes()).hexdigest(),'9524fee019274e2a5fd57b5ed8ff570dc7b63525f324e9f654efc8f6da0c85ec')
  rows=source_functions()+source_functions(True);src=self.directory/'typed.ink';src.write_text('module Algebra20Typed;\n'+'\n'.join(text for _,text in rows)+'\n');core=self.directory/'typed.core.json';subject=self.directory/'typed.semantic.json'
  self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject);original=json.loads(subject.read_text());derived=specialize(original);self.assertEqual(len(derived),28)
  deps=[(n,l) for n,l in prior_sum_laws() if n in {'mapped_sum_u32','mapped_sum_i32','mapped_sum_u64'}]
  st,m=publish(self.directory/'isolated',derived+deps);self.assertEqual(len(st.members()),42);admission=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json')
  searches=[];apps=[];old_controls=[]
  for heldout in (False,True):
   for t in ('u32','i32','u64','f32'):
    group=source_functions(heldout,t);unit=self.directory/f'{t}-{int(heldout)}.ink';unit.write_text('module Unit20;\n'+'\n'.join(text for _,text in group)+'\n');uc=unit.with_suffix('.core.json');out=unit.with_suffix('.selection.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc)
    r=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',4096,'--compact-output','-o',out);searches.append(json.loads(r.stdout));selection=json.loads(out.read_text());self.assertEqual(len(selection['applications']),len(group));apps+=selection['applications'];self.assertFalse(json.loads(r.stdout).get('exhausted',False))
    self.run_command(COMPILER,'check-selection',uc,out)
    # Raw immutable prior source control is separate from the root's symmetric
    # old-only beta certificate overlay used for final performance attribution.
    if t=='u32':
     prior=unit.with_suffix('.prior.selection.json');r=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',ROOT,'--snapshot',ROOT/'store/snapshots'/f'{PIN}.json','--cost-model',COST,'--budget',4096,'--compact-output','-o',prior)
     oldselection=json.loads(prior.read_text());self.run_command(COMPILER,'check-selection',uc,prior)
     oldcore=unit.with_suffix('.prior.core.json');newcore=unit.with_suffix('.selected.core.json');self.run_command(COMPILER,'emit-core',unit,'--selection',prior,'-o',oldcore);self.run_command(COMPILER,'emit-core',unit,'--selection',out,'-o',newcore)
     olds=unit.with_suffix('.prior.semantic.json');news=unit.with_suffix('.selected.semantic.json');self.run_command(COMPILER,'emit-semantic',oldcore,'--core','-o',olds);self.run_command(COMPILER,'emit-semantic',newcore,'--core','-o',news);oldterms=json.loads(olds.read_text())['functions'];newterms=json.loads(news.read_text())['functions'];self.assertTrue(all(oldterms[n]!=newterms[n] for n,_ in group));old_controls.append(dict(functions=[n for n,_ in group],applications=oldselection['applications'],search=json.loads(r.stdout),scope='Raw prior catalogue only; final fair old-only normalization overlay is root-owned.'))
  combined=self.directory/'combined.selection.json';combined.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=original['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');replay=self.run_command(COMPILER,'check-selection',core,combined);selected=self.directory/'selected.core.json';self.run_command(COMPILER,'emit-core',src,'--selection',combined,'-o',selected)
  records=[]
  for name,_ in rows:
   t=name.replace('_heldout','').rsplit('_',1)[1];heldout=name.endswith('_heldout');family='sum' if 'mapper_sum' in name else 'count' if 'predicate_count' in name else 'fold'
   for index,args in enumerate(frames(t)):
    path=self.directory/f'args-{t}-{index}.json';path.write_text(json.dumps(args)+'\n');literal=reference(args,t,heldout,family,True);math_ref=reference(args,t,heldout,family,False)
    before=json.loads(self.run_command(COMPILER,'run',src,name,path).stdout);after=json.loads(self.run_command(COMPILER,'run',selected,name,path,'--core').stdout);self.assertEqual(before,after)
    if t=='f32' and family=='fold':
     actual=number(before)
     if math.isnan(literal):self.assertTrue(math.isnan(actual) and math.isnan(math_ref))
     else:self.assertEqual(struct.pack('<f',literal),struct.pack('<f',math_ref));self.assertEqual(struct.pack('<f',literal),struct.pack('<f',actual))
    else:self.assertEqual(literal,math_ref);self.assertEqual(before,math_ref)
    records.append(dict(function=name,type=t,arguments=args,original=before,selected=after,mathematical_reference=math_ref if not isinstance(math_ref,float) or math.isfinite(math_ref) else str(math_ref)))
  (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'static-witnesses.json').write_text(json.dumps([dict(name=n,law=l) for n,l in derived],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(generic_roots=11,mechanisms=3,source_instances=22,sum_fold_compositions=6,dependency_roots=3,isolated_entries=len(st.members()),frames=len(records),actual_interpreter_runs=2*len(records),fresh_selected_applications=len(apps),admission=json.loads(admission.stdout),replay=json.loads(replay.stdout),searches=searches,raw_prior_controls=old_controls),indent=2)+'\n')
 def test_hash_valid_false_endpoints_rejected_semantically(self):
  src=self.directory/'negative.ink';src.write_text('module Negative20;\n'+source_functions(t='u32')[0][1]+'\n');core=src.with_suffix('.core.json');self.run_command(COMPILER,'emit-core',src,'-o',core);failures=[]
  for family in ('mapper_sum','predicate_count','arbitrary_fold'):
   bad=copy.deepcopy(dict(named_laws())['gated_'+family+'_u32']);bad['to']=word('U64' if family=='predicate_count' else 'U32',1)
   st,_=publish(self.directory/family,[(family+'_false',bad)]);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(family=family,content_id=identity(semantic_entry(bad)),stderr=r.stderr))
  (self.directory/'false-endpoints.json').write_text(json.dumps(failures,indent=2)+'\n')
 def test_source_specialization_checks_false_branch(self):
  text=source_functions(t='u32')[0][1].replace(',0)))',',k)))');self.assertNotEqual(text,source_functions(t='u32')[0][1]);src=self.directory/'wrong-fallback.ink';src.write_text('module Wrong20;\n'+text+'\n');core=src.with_suffix('.core.json');subject=src.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject);rows=specialize(json.loads(subject.read_text()));self.assertEqual(len(rows),2)
  deps=[(n,l) for n,l in prior_sum_laws() if n=='mapped_sum_u32'];st,_=publish(self.directory/'wrong-store',rows+deps);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);(self.directory/'false-specialization.json').write_text(json.dumps(dict(content_ids=[identity(semantic_entry(l)) for _,l in rows],stderr=r.stderr),indent=2)+'\n')

if __name__=='__main__':unittest.main()
