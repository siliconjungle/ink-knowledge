"""Checked reusable accepted-branch specialization, fairness and exact typed values."""
import copy,hashlib,json,math,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import arrow,bound,lam,law,op,value,var,word
from producers.web_accepted25_laws import named_laws,root_laws,source_functions,specialize,publish,law_roles,PIN
ROOT=Path(__file__).resolve().parents[1];COMPILER=ROOT.parent.parent/'toolchain/ink-demand-proofs';COST=ROOT.parent/'reports/web-stack-proofs-24-2026-10-11/cpu-cost-model.json'
def alpha(v):
 seen={}
 def visit(x):
  if isinstance(x,dict):
   if set(x)=={'Free'}:n=x['Free'];seen.setdefault(n,'v'+str(len(seen)));return {'Free':seen[n]}
   return {k:visit(x[k]) for k in sorted(x)}
  if isinstance(x,list):return [visit(y) for y in x]
  return x
 return canonical(visit([v['from'],v['to']]))
def number(x):return struct.unpack('<f',struct.pack('<I',x['F32Bits']))[0] if isinstance(x,dict) else x
def norm(x,t):
 if t=='f32':
  try:return struct.unpack('<f',struct.pack('<f',x))[0]
  except OverflowError:return math.copysign(math.inf,x)
 x&=(1<<(64 if t=='u64' else 32))-1
 return x-(1<<32) if t=='i32' and x>=1<<31 else x
def div(a,b,t,remainder=False):
 if not b or (t=='i32' and a==-(1<<31) and b==-1):return 0
 q=abs(a)//abs(b)*(1 if (a<0)==(b<0) else -1)
 return a-q*b if remainder else q

def oracle(name,args,staged):
 t=name.rsplit('_',1)[1];n=lambda x:norm(x,t);xs,seed,k=args;xs=[n(number(x)) for x in xs];seed,k=n(number(seed)),n(number(k));held='heldout' in name;calls=[0]
 def predicate(x):
  calls[0]+=1
  if t=='f32':return (n(x+k) if x<seed else n(x-k))>k if held else (n(x-seed) if x>k else n(seed-x))<k
  return (div(n(seed-x) if x<seed else n(x-seed),k,t,True)<div(k,2,t)) if held else div(x,seed,t,True)<k
 f=lambda x:(n(n(x*k)-seed) if x>k else n(seed+x)) if held else (n(seed-x) if x<seed else n(x+seed))
 g=lambda x:(n(x+seed) if x<k else n(x-k)) if held else (n(x-seed) if x>seed else n(x*k))
 if staged:
  accepted=[x for x in xs if predicate(x)];mapped=[f(x) if predicate(x) else g(x) for x in accepted]
 else:mapped=[f(x) for x in xs if predicate(x)]
 if 'repair' in name:return mapped,calls[0]
 if 'total' in name:
  result=n(0)
  for x in mapped:result=n(result+x)
  return result,calls[0]
 result=seed
 for x in reversed(mapped):result=n(x+n(result*k)) if result<seed else n(x-result)
 return result,calls[0]

def frames(t):
 r=random.Random(2501)
 if t=='f32':
  nan={'F32Bits':0x7fc00123};inf={'F32Bits':0x7f800000};neg={'F32Bits':0xff800000}
  return [[[],2.0,3.0],[[0.0,-0.0,1.0,2.0,3.0,8.0],2.0,3.0],[[nan,inf,neg,0.0,-0.0],2.0,-3.0],[[0.0,-0.0,1.0,-1.0],nan,2.0],[[0.0,-0.0,1.0,-1.0],2.0,nan],[[0.0,-0.0,1.0,-1.0],-0.0,inf],[[1e20,-1e20,1.5,-2.0],-2.0,1e20],[[0.0,-0.0,1.0,-1.0],neg,-2.0],[[r.randrange(-1000,1000)/8 for _ in range(19)],17.25,-3.0]]
 bits=64 if t=='u64' else 32;n=lambda x:norm(x,t);hi=(1<<31)-1 if t=='i32' else (1<<bits)-1;lo=-(1<<31) if t=='i32' else 0
 return [[[],7,3],[[0,1,7,8,hi,lo],7,3],[[hi,lo,hi,1,0],0,0],[[1,2,3,4,5],0,7],[[0,1,2,3,4,5,hi],7,0],[[lo,hi,0,1],n(-1),n(-1)],[[n(r.getrandbits(bits)) for _ in range(19)],n(r.getrandbits(bits)),n(r.getrandbits(bits))]]

class Accepted25Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];archive=os.environ.get('INK_ACCEPTED25_EVIDENCE')
  if archive:self.directory=Path(archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True);self.archive=True
  else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-accepted25-');self.directory=Path(self.tmp.name);self.archive=False
 def tearDown(self):
  if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def command(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),text=True,capture_output=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def compile(self,name,text):
  src=self.directory/(name+'.ink');src.write_text('module Accepted25;\n'+text+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');self.command(COMPILER,'emit-core',src,'-o',core);self.command(COMPILER,'emit-semantic',core,'--core','-o',sem);return src,core,json.loads(sem.read_text())
 def assert_value(self,actual,expected,t):
  if isinstance(expected,list):
   self.assertEqual(len(actual),len(expected))
   for a,b in zip(actual,expected):self.assert_value(a,b,t)
  elif t=='f32':
   a=number(actual)
   if math.isnan(expected):self.assertTrue(math.isnan(a))
   else:self.assertEqual(struct.pack('<f',a),struct.pack('<f',expected))
  else:self.assertEqual(actual,expected)
 def test_novelty_and_full_prior_first_step_opportunities(self):
  from producers.beta_sharing17 import derive
  old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1724);self.assertEqual(len(named_laws()),9);self.assertEqual(list(law_roles().values()).count('optimization_endpoint'),4);self.assertEqual(list(law_roles().values()).count('deployment_composition'),5)
  endpoints={alpha(v) for _,v in named_laws()};self.assertEqual(len(endpoints),9);generic=[]
  for i in sorted(old.members()):
   o=old.object(i);v=dict(o['payload'],schema=1,semantics=o['semantics'],dependencies=o['dependencies'])
   if all(k in v for k in ['params','from','to','proof']) and isinstance(v['from'],dict) and 'node' in v['from']:
    self.assertNotIn(alpha(v),endpoints);generic.append(('prior_'+i,v))
  records=[];accepted=[]
  for name,t,text in source_functions()+source_functions(True):
   if t!='u32':continue
   src,core,subject=self.compile(name,text);checks=[]
   for j,(label,v) in enumerate(derive(subject,generic)):
    objects=list(old.bundle(v['dependencies'])['objects'].values())+[semantic_entry(v)];st=Store.publish(self.directory/(name+'-old-'+str(j)),objects,{label:identity(semantic_entry(v))});view=st.root/'view.json';view.write_bytes(canonical(st.bundle([identity(semantic_entry(v))]))+b'\n');r=self.command(COMPILER,'knowledge-check',core,view,success=False);checks.append(dict(name=label,id=identity(semantic_entry(v)),exit_code=r.returncode,stderr=r.stderr,target=v['to']))
    if r.returncode==0:accepted.append((label,v))
   # Admit every old opportunity; no empty-old-frontier assertion or cost tuning.
   records.append(dict(function=name,proposals=checks,accepted_first_steps=sum(c['exit_code']==0 for c in checks)))
  (self.directory/'old-opportunities.json').write_text(json.dumps(dict(prior_snapshot=PIN,prior_entries=1724,old_semantic_laws=len(generic),sources=records,accepted_source_witnesses=[dict(name=n,law=v) for n,v in accepted],scope='Every historical semantic candidate offered and all outcomes preserved. This author probe is first-step; root serial integration offers bounded old composed certificates symmetrically before measuring.'),indent=2)+'\n')
 def test_typed_default_replay_reification_and_complete_oracles(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'b84caa0b9fbdc4166338b3c31dc90d1f7045d14cf1e7c0abacf9f911146fd438');rows=source_functions()+source_functions(True);src,core,subject=self.compile('all','\n'.join(s for _,_,s in rows));derived=specialize(subject);self.assertEqual(len(derived),26);st=publish(self.directory/'isolated',derived);admit=self.command(COMPILER,'knowledge-check',core,st.root/'view.json');apps=[];searches=[]
  for name,t,text in rows:
   unit,uc,_=self.compile(name,text);selection=unit.with_suffix('.selection.json');r=self.command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',512,'--compact-output','-o',selection);searches.append(json.loads(r.stdout));s=json.loads(selection.read_text());self.assertEqual(len(s['applications']),1,(name,s['applications']));apps+=s['applications']
  sel=self.directory/'all.selection.json';sel.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');replay=self.command(COMPILER,'check-selection',core,sel);selected=self.directory/'selected.core.json';self.command(COMPILER,'emit-core',src,'--selection',sel,'-o',selected);sem=selected.with_suffix('.semantic.json');self.command(COMPILER,'emit-semantic',selected,'--core','-o',sem);terms=json.loads(sem.read_text())['functions'];records=[]
  for name,t,text in rows:
   encoded=json.dumps(terms[name]);self.assertEqual(encoded.count('call:foldr'),int('checksum' in name))
   if 'checksum' in name:self.assertNotIn('method:map',encoded);self.assertNotIn('method:filter',encoded)
   if 'total' in name:self.assertNotIn('method:filter',encoded);self.assertIn('call:sum',encoded)
   for i,args in enumerate(frames(t)):
    path=self.directory/f'args-{t}-{i}.json';path.write_text(json.dumps(args)+'\n');before=json.loads(self.command(COMPILER,'run',src,name,path).stdout);after=json.loads(self.command(COMPILER,'run',selected,name,path,'--core').stdout);self.assertEqual(before,after);a,ac=oracle(name,args,True);b,bc=oracle(name,args,False);self.assert_value(before,a,t);self.assert_value(after,b,t);self.assertLessEqual(bc,ac)
    records.append(dict(function=name,type=t,arguments=args,original=before,selected=after,oracle_staged_predicate_calls=ac,oracle_fused_predicate_calls=bc))
  (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v) for n,v in derived],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(generic_roots=4,deployment_compositions=5,typed_source_certificates=len(derived),default_selected_functions=len(rows),typed_frames=len(records),interpreter_runs=2*len(records),admission=json.loads(admit.stdout),replay=json.loads(replay.stdout),searches=searches,gpu_builds=0,timing_calls=0),indent=2)+'\n')
 def test_hash_valid_false_controls_and_capture_safety(self):
  src,core,_=self.compile('controls',source_functions()[0][2]);base=root_laws()[0][1];bad_branch=copy.deepcopy(base);bad_branch['to']['node']['Op'][1][1]=var(arrow(value('U32'),value('U32')),'g');bad_filter=copy.deepcopy(base);bad_filter['to']['node']['Op'][1][0]=var(value({'List':'U32'}),'xs');failures=[]
  for label,v in [('wrong-selected-mapper',bad_branch),('dropped-filter',bad_filter)]:
   st=publish(self.directory/label,[(label,v)]);r=self.command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(label=label,id=identity(semantic_entry(v)),stderr=r.stderr))
  # A structurally different predicate cannot be assumed equivalent by the producer.
  _,_,subject=self.compile('wrong-condition','pub fn unrelated(xs:List<u32>,seed:u32,k:u32)->List<u32>{return xs.filter(fn(x)=>x<seed).map(fn(x)=>choose(x<k,x+seed,x-k));}')
  self.assertEqual(specialize(subject),[])
  # Bound-variable index and free captures survive inside a nested lambda.
  _,_,nested=self.compile('nested-capture','pub fn arbitrary_export(xs:List<u32>,seed:u32,k:u32)->List<u32>{return xs.filter(fn(x)=>x<seed).map(fn(x)=>choose(x<seed,foldr(xs,seed,fn(y)=>fn(a)=>y-a+x*k),x+k));}')
  certs=specialize(nested);self.assertEqual(len(certs),1);st=publish(self.directory/'nested',certs);self.command(COMPILER,'knowledge-check',core,st.root/'view.json')
  (self.directory/'controls.json').write_text(json.dumps(dict(false_controls=failures,counterexamples=dict(wrong_branch=dict(xs=[1],predicate='true',f='x+1',g='x+2',source=[2],false_target=[3]),dropped_filter=dict(xs=[1,7],predicate='x<3',f='x+1',source=[2],false_target=[2,8])),different_predicate_unmatched=True,nested_capture_checked=True),indent=2)+'\n')
if __name__=='__main__':unittest.main()
