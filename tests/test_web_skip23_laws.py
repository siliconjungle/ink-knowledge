"""Complete checked deployment/value tests for demand-driven consumers."""
import copy,hashlib,json,math,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import word,var,value
from producers.web_skip23_laws import named_laws,old_composition_laws,law_roles,publish,source_functions,specialize
ROOT=Path(__file__).resolve().parents[1];COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs';PIN='95c096ab4a28114fb70c334b662057bd8abfffe135a3198032f4ea38a679bd57';COST=ROOT.parent/'reports/web-stack-proofs-22-2026-10-11/cpu-cost-model.json'
def alpha(l):
 names={}
 def walk(v):
  if isinstance(v,dict):
   if set(v)=={'Free'}:names.setdefault(v['Free'],'v'+str(len(names)));return {'Free':names[v['Free']]}
   return {k:walk(v[k]) for k in sorted(v)}
  if isinstance(v,list):return [walk(x) for x in v]
  return v
 return canonical(walk([l['from'],l['to'],l.get('conditions',[])]))
def decode(v):return struct.unpack('<f',struct.pack('<I',v['F32Bits']))[0] if isinstance(v,dict) else v
def norm(v,t):
 if t=='f32':
  try:return struct.unpack('<f',struct.pack('<f',v))[0]
  except OverflowError:return math.copysign(float('inf'),v)
 if t=='bool':return bool(v)
 v&=(1<<(64 if t=='u64' else 32))-1
 return v-(1<<32) if t=='i32' and v>=1<<31 else v
def key(v,t):return struct.unpack('<I',struct.pack('<f',decode(v)))[0] if t=='f32' else v
def predicate(x,seed,k,t,h):return x==(k if h else seed) if t=='bool' else x<k if h else x>seed
def mapper(x,seed,k,t,h):return norm(x+k if x<seed else x-seed,t) if h else norm(x-k if x>k else x+k,t)
def literal(args,t,h,mapped,count):
 xs,seed,k=args;seed,k=decode(seed),decode(k);selected=[x for x in xs if predicate(decode(x),seed,k,t,h)]
 if count:return len(selected)+len([x for x in xs if not predicate(decode(x),seed,k,t,h)])
 values=[mapper(decode(x),seed,k,t,h) for x in selected] if mapped else selected
 return values[0] if values else args[1]
def reference(args,t,h,mapped,count):
 if count:return len(args[0])
 seed,k=map(decode,args[1:])
 for raw in args[0]:
  x=decode(raw)
  if predicate(x,seed,k,t,h):return mapper(x,seed,k,t,h) if mapped else raw
 return args[1]
def frames(t):
 if t=='bool':return [[[],False,True],[[False,True,True],False,True],[[True]*3,True,False],[[False]*4,True,False]]
 if t=='f32':return [[[],0.5,1.0],[[0.0,-0.0,1.0,-1.0],0.5,1.0],[[0.0,0.25,0.75,1.5],0.5,1.0],[[0.0,0.25],2.0,-1.0],[[{'F32Bits':0x7fc01234},-0.0,{'F32Bits':0x7f800000},{'F32Bits':0xff800000}],0.25,2.0],[[0.0,-0.0,1.5],{'F32Bits':0x7fc01234},1.0],[[0.0,-0.0],-1.0,2.0],[[1.0,2.0],3.0,{'F32Bits':0x7fc00000}]]
 bits=64 if t=='u64' else 32;w=lambda x:norm(x,t);rng=random.Random(2323);hi=w((1<<bits)-1);return [[[],7,3],[[0,1,9,3],7,3],[[9,1,0],7,3],[[0,1,2],7,0],[[w(-1),0,1,w(1<<31),w((1<<31)-1)],7,3],[[0,1,2],0,hi],[[w(rng.getrandbits(bits)) for _ in range(17)],w(-3),7],[[1,1,1],1,1]]
class Skip23Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];self.archive=os.environ.get('INK_SKIP23_EVIDENCE')
  if self.archive:self.directory=Path(self.archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
  else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-skip23-');self.directory=Path(self.tmp.name)
 def tearDown(self):
  if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def run_command(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def test_novelty_roles_and_checked_old_opportunity(self):
  prior=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(prior.members()),1648);rows=named_laws();self.assertEqual(len(rows),12);self.assertEqual(list(law_roles().values()).count('optimization_endpoint'),8);self.assertEqual(list(law_roles().values()).count('deployment_composition'),4);endpoints={alpha(l) for _,l in rows};self.assertEqual(len(endpoints),12)
  for i in prior.members():
   l=prior.object(i)['payload']
   if isinstance(l.get('from'),dict) and 'node' in l['from']:self.assertNotIn(alpha(l),endpoints)
  for _,l in old_composition_laws():self.assertTrue(set(l['dependencies'])<=set(prior.members()));self.assertNotIn(alpha(l),endpoints)
  self.assertTrue(all(('skip_first_accepted_'+n.rsplit('_',1)[1] in dict(named_laws())) and identity(semantic_entry(dict(named_laws())['skip_first_accepted_'+n.rsplit('_',1)[1]])) in l['dependencies'] for n,l in rows if 'mapped_first' in n))
  (self.directory/'novelty.json').write_text(json.dumps(dict(snapshot=PIN,prior_entries=1648,roles=law_roles(),old_composition_ids=[identity(semantic_entry(l)) for _,l in old_composition_laws()],names={n:identity(semantic_entry(l)) for n,l in rows}),indent=2)+'\n')
 def test_typed_application_replay_reification_and_complete_values(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08');rows=source_functions()+source_functions(True);self.assertEqual(len(rows),26);src=self.directory/'typed.ink';src.write_text('module Typed23;\n'+'\n'.join(s for _,s in rows)+'\n');core=src.with_suffix('.core.json');subject=src.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject);original=json.loads(subject.read_text());static=specialize(original);self.assertEqual(len(static),26);st=publish(self.directory/'isolated',static);self.assertEqual(len(st.members()),50);admission=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json');apps=[];searches=[]
  for h in (False,True):
   for t in ('u32','i32','u64','f32','bool'):
    group=source_functions(h,t);unit=self.directory/f'{t}-{int(h)}.ink';unit.write_text('module Unit23;\n'+'\n'.join(s for _,s in group)+'\n');uc=unit.with_suffix('.core.json');out=unit.with_suffix('.selection.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc);r=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',4096,'--compact-output','-o',out);searches.append(json.loads(r.stdout));self.assertFalse(searches[-1]['exhausted']);selection=json.loads(out.read_text());self.assertEqual(len(selection['applications']),len(group));apps+=selection['applications'];self.run_command(COMPILER,'check-selection',uc,out)
  package=self.directory/'combined.selection.json';package.write_bytes(canonical(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=original['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps))+b'\n');replay=self.run_command(COMPILER,'check-selection',core,package);selected=self.directory/'selected.core.json';self.run_command(COMPILER,'emit-core',src,'--selection',package,'-o',selected);sem=self.directory/'selected.semantic.json';self.run_command(COMPILER,'emit-semantic',selected,'--core','-o',sem);current=json.loads(sem.read_text())['functions'];records=[]
  for name,_ in rows:
   h=name.endswith('_heldout');t=name.replace('_heldout','').rsplit('_',1)[1];count='partition_count' in name;mapped='mapped_first' in name;wire=json.dumps(current[name]);self.assertNotIn('method:filter',wire);self.assertNotIn('method:map',wire);self.assertEqual(wire.count('call:foldr'),0 if count else 1)
   for i,args in enumerate(frames(t)):
    path=self.directory/f'args-{t}-{i}.json';path.write_text(json.dumps(args)+'\n');a=json.loads(self.run_command(COMPILER,'run',src,name,path).stdout);b=json.loads(self.run_command(COMPILER,'run',selected,name,path,'--core').stdout);expected=reference(args,t,h,mapped,count);staged=literal(args,t,h,mapped,count);output='u64' if count else t;self.assertEqual(key(a,output),key(b,output));self.assertEqual(key(a,output),key(expected,output));self.assertEqual(key(staged,output),key(expected,output));records.append(dict(function=name,type=t,args=args,original=a,selected=b,reference=({'F32Bits':key(expected,output)} if output=='f32' and not math.isfinite(decode(expected)) else expected),reference_bits=key(expected,output)))
  (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'static-witnesses.json').write_text(json.dumps([dict(name=n,law=l) for n,l in static],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(fresh_generic=12,old_composed=1,historical_dependencies=11,static_test_instances=26,isolated_objects=50,frames=len(records),actual_interpreter_runs=2*len(records),selected_functions=len(rows),application_count=len(apps),admission=json.loads(admission.stdout),replay=json.loads(replay.stdout),searches=searches),indent=2)+'\n')
 def test_hash_valid_false_endpoints_reject_semantically(self):
  src=self.directory/'negative.ink';src.write_text('module Negative23;\n'+source_functions(t='u32')[0][1]+'\n');core=src.with_suffix('.core.json');self.run_command(COMPILER,'emit-core',src,'-o',core);failures=[]
  for family in ('skip_partition_count','skip_first_accepted','skip_mapped_first_accepted'):
   bad=copy.deepcopy(dict(named_laws())[family+'_u32']);bad['to']=word('U64' if 'count' in family else 'U32',1);st=publish(self.directory/family,[(family+'_false',bad)]);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertNotIn('identity mismatch',r.stderr);self.assertTrue('semantic normal forms differ' in r.stderr or 'does not match exact application' in r.stderr);failures.append(dict(family=family,id=identity(semantic_entry(bad)),stderr=r.stderr))
  (self.directory/'false-endpoints.json').write_text(json.dumps(failures,indent=2)+'\n')
 def test_source_correlations_and_first_index_rejected(self):
  count=source_functions(t='u32')[0][1];first=source_functions(t='u32')[1][1];wrongcount=count.replace('(x>seed)==false','x>seed');different=count.rsplit('count(xs.filter',1);different=different[0]+'count(ys.filter'+different[1];different=different.replace('(xs:List<u32>,','(xs:List<u32>,ys:List<u32>,');failures=[]
  for label,text in [('wrong-complement',wrongcount),('wrong-receiver',different),('wrong-index',first.replace('.at_or(0,seed)','.at_or(1,seed)'))]:
   src=self.directory/(label+'.ink');src.write_text('module Correlation23;\n'+text+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',sem);candidates=specialize(json.loads(sem.read_text()));self.assertEqual(len(candidates),1);st=publish(self.directory/label,candidates);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(label=label,id=identity(semantic_entry(candidates[0][1])),stderr=r.stderr))
  (self.directory/'false-correlations.json').write_text(json.dumps(failures,indent=2)+'\n')
if __name__=='__main__':unittest.main()
