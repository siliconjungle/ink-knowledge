"""Aligned nested independent zip: ordinary proofs and complete typed values."""
import copy,hashlib,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.web_zip27_laws import named_laws,grouped_laws,source_functions,specialize,law_roles
from producers.beta_sharing17 import derive
from knowledge.tests.test_web_zip17_laws import alpha,decode,normalize,key,frames as previous_frames
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent
COMPILER=REPO.parent/'toolchain/ink-direct-js-proofs'
PIN='a2a756dc7174ab62c2806e09dd0e3769e507f4ed5e455d687346c544cd788abd'
SHA='719fd6ff95ea7cd600d7f4078677b46c46fdd545ef2b21ae5643ca5eba085787'
COST=REPO/'reports/web-stack-proofs-26-2026-10-11/cpu-cost-model.json'

def frames(t):
 rows=previous_frames(t)
 if t=='f32':
  edge=[{'F32Bits':0x80000000},{'F32Bits':0xffc01234},{'F32Bits':0x7f800000},{'F32Bits':0xff800000},1.25,-2.5]
  for seed,k in [({'F32Bits':0x7f800000},-2.0),({'F32Bits':0xff800000},2.0),(1.0,{'F32Bits':0x7f800000}),(1.0,{'F32Bits':0xff800000})]:
   rows.append([edge,list(reversed(edge)),seed,k])
 return rows

def oracle(name,args,eager):
 t=next(t for t in ('u32','i32','u64','f32') if '_'+t in name);held=name.endswith('_heldout');left='_left_' in name
 xs,ys,seed,k=args;xs,ys=list(map(decode,xs)),list(map(decode,ys));seed,k=decode(seed),decode(k);w=lambda v:normalize(v,t)
 def h(a,b):
  if held:return w(w(a*b)+k) if b>seed else w(a+b)
  return w(a+w(b*k)) if a<seed else w(a-b)
 def g(v,x):
  if held:return w(w(v*k)+x) if x<k else w(v+w(x*seed))
  return w(v+w(x*k)) if v<seed else w(v-x)
 if eager:
  values=[h(a,b) for a,b in zip(xs,ys)]
  return [g(v,x) for v,x in zip(values,xs if left else ys)]
 return [g(h(xs[i],ys[i]),xs[i] if left else ys[i]) for i in range(min(len(xs),len(ys)))]

def publish(q,rows):
 objects={identity(semantic_entry(v)):semantic_entry(v) for _,v in rows};st=Store.publish(q,list(objects.values()));st.rebuild();view=q/'view.json';view.write_bytes(canonical(st.bundle(sorted(objects)))+b'\n');return st,view

class Zip27Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];p=os.environ.get('INK_ZIP27_EVIDENCE');self.archived=bool(p)
  if p:self.q=Path(p)/self._testMethodName;self.q.mkdir(parents=True,exist_ok=True)
  else:self.tmp=tempfile.TemporaryDirectory(prefix='zip27-');self.q=Path(self.tmp.name)
 def tearDown(self):
  if self.archived:(self.q/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def cmd(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(command=r.args,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def compile(self,name,text):
  src=self.q/(name+'.ink');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');src.write_text('module Zip27;\n'+text+'\n');self.cmd(COMPILER,'emit-core',src,'-o',core);self.cmd(COMPILER,'emit-semantic',core,'--core','-o',sem);return src,core,json.loads(sem.read_text())
 def values(self,a,b,t):
  import math
  self.assertEqual(len(a),len(b))
  for x,y in zip(a,b):
   if t=='f32' and math.isnan(decode(y)):self.assertTrue(math.isnan(decode(x)))
   else:self.assertEqual(key(x,t),key(y,t))
 def test_alpha_novelty_and_all_prior_first_step_opportunities(self):
  old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1790);rows=named_laws();self.assertEqual(len(rows),16)
  supports,roots=grouped_laws();self.assertEqual((len(supports),len(roots)),(8,8));self.assertEqual(list(law_roles().values()).count('optimization_endpoint'),8)
  new={alpha(v) for _,v in rows};self.assertEqual(len(new),16);generic=[]
  for i in sorted(old.members()):
   o=old.object(i);v=dict(o['payload'],schema=1,semantics=o['semantics'],dependencies=o['dependencies'])
   if all(k in v for k in ('from','to','params','proof')) and isinstance(v['from'],dict) and 'node' in v['from']:
    self.assertNotIn(alpha(v),new);generic.append(('prior_'+i,v))
  records=[]
  for n,t,text in source_functions():
   if t!='u32':continue
   _,core,subject=self.compile(n,text);proposed=derive(subject,generic);checks=[]
   for j,(label,v) in enumerate(proposed):
    objects=list(old.bundle(v['dependencies'])['objects'].values())+[semantic_entry(v)];st=Store.publish(self.q/(n+'-old-'+str(j)),objects);view=st.root/'view.json';view.write_bytes(canonical(st.bundle([identity(semantic_entry(v))]))+b'\n');r=self.cmd(COMPILER,'knowledge-check',core,view,success=False);checks.append(dict(name=label,law=v,id=identity(semantic_entry(v)),exit_code=r.returncode,stderr=r.stderr))
   records.append(dict(function=n,checks=checks,accepted=sum(r['exit_code']==0 for r in checks)))
  (self.q/'novelty.json').write_text(json.dumps(dict(prior_snapshot=PIN,prior_entries=1790,prior_semantic_laws=len(generic),new_generic_endpoints=8,proof_supports=8,identities=2,prior_first_step=records,scope='All prior semantic candidates offered; first step only. Parent independently derives full bounded four-application/128-body fair opportunities.'),indent=2)+'\n')
 def test_all_typed_bridges_default_selection_replay_and_values(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA);sources=source_functions()+source_functions(True)
  _,allcore,subject=self.compile('all','\n'.join(s for _,_,s in sources));certs=specialize(subject);self.assertEqual(len(certs),16);st,view=publish(self.q/'isolated',named_laws()+certs);admit=self.cmd(COMPILER,'knowledge-check',allcore,view)
  (self.q/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v) for n,v in certs],indent=2)+'\n');records=[];plans=[]
  for name,t,text in sources:
   src,core,one=self.compile(name,text);selection=self.q/(name+'.selection.json');r=self.cmd(sys.executable,REPO/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',512,'--compact-output','-o',selection);p=json.loads(selection.read_text());self.assertEqual(len(p['applications']),1);self.assertEqual(p['applications'][0]['function'],name);self.cmd(COMPILER,'check-selection',core,selection);selected=self.q/(name+'.selected.core.json');self.cmd(COMPILER,'emit-core',src,'--selection',selection,'-o',selected);before=json.loads(core.read_text())['program']['functions'][0]['body'];after=json.loads(selected.read_text())['program']['functions'][0]['body'];self.assertNotEqual(before,after);plans.append(dict(function=name,search=json.loads(r.stdout),applications=p['applications'],selected_core_sha256=hashlib.sha256(selected.read_bytes()).hexdigest()))
   for i,args in enumerate(frames(t)):
    argument=self.q/(name+'-args-'+str(i)+'.json');argument.write_text(json.dumps(args)+'\n');a=json.loads(self.cmd(COMPILER,'run',core,name,argument,'--core').stdout);b=json.loads(self.cmd(COMPILER,'run',selected,name,argument,'--core').stdout);self.assertEqual(a,b);eager=oracle(name,args,True);fused=oracle(name,args,False);self.values(fused,eager,t);self.values(a,eager,t);records.append(dict(function=name,type=t,args=args,original=a,selected=b,expected=[{'F32Bits':key(x,t)} if t=='f32' else x for x in eager]))
  (self.q/'selection-comparison.json').write_text(json.dumps(plans,indent=2)+'\n');(self.q/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.q/'scope.json').write_text(json.dumps(dict(admission=json.loads(admit.stdout),generic_objects=16,source_certificates=16,selected_functions=len(plans),typed_frames=len(records),interpreter_calls=len(records)*2,independent_eager_and_fused_oracles=True,gpu_builds=0,timing_calls=0),indent=2)+'\n')
 def test_hash_valid_wrong_alignment_controls(self):
  _,core,_=self.compile('false',source_functions()[0][2]);supports,roots=grouped_laws();supportobjects={identity(semantic_entry(v)):semantic_entry(v) for _,v in supports};results=[]
  for n,v in roots[:2]:
   bad=copy.deepcopy(v);zipper=bad['to']['node']['Op'][1][2];body=zipper['node']['Lambda']['node']['Lambda'];body['node']['Op'][1][1]['node']['Bound']=0 if '_left_' in n else 1
   objects=[supportobjects[i] for i in bad['dependencies']]+[semantic_entry(bad)];st=Store.publish(self.q/n,objects);view=st.root/'view.json';view.write_bytes(canonical(st.bundle([identity(semantic_entry(bad))]))+b'\n');r=self.cmd(COMPILER,'knowledge-check',core,view,success=False);self.assertNotEqual(r.returncode,0);self.assertNotIn('identity mismatch',r.stderr);self.assertTrue(any(s in r.stderr for s in ['semantic normal forms differ','condition does not establish goal','law does not match exact application endpoints']));results.append(dict(name=n,id=identity(semantic_entry(bad)),stderr=r.stderr))
  # Distinct finite receivers must not match the aligned same-receiver rule.
  _,_,unaligned=self.compile('unaligned','pub fn different(xs:List<u32>,ys:List<u32>,zs:List<u32>,seed:u32)->List<u32>{return xs.zip(ys,fn(a)=>fn(b)=>a+b).zip(zs,fn(v)=>fn(z)=>v+z);}')
  self.assertEqual(specialize(unaligned),[])
  # Capture/shadowing exercise for static curried callback sharing, checked
  # independently from ordinary export names and without runtime checks.
  capture='pub fn capture(xs:List<u32>,ys:List<u32>,seed:u32,k:u32)->List<u32>{return xs.zip(ys,fn(xs)=>fn(y)=>choose(xs<seed,xs+y*k,xs-y)).zip(ys,fn(seed)=>fn(k)=>choose(seed<k,seed+k,seed-k));}'
  csrc,ccore,csubject=self.compile('capture',capture);cert=specialize(csubject);self.assertEqual(len(cert),1);cstore,cview=publish(self.q/'capture-store',named_laws()+cert);self.cmd(COMPILER,'knowledge-check',ccore,cview)
  _,witness=cert[0];oid=identity(semantic_entry(witness));selection=self.q/'capture.selection.json';selection.write_bytes(canonical(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=csubject['input_core_sha256'],knowledge=cstore.bundle([oid]),applications=[dict(function='capture',path=[],law=oid,arguments={n:{'sort':s,'node':{'Free':n}} for n,s in witness['params'].items()},premises=[])]))+b'\n');self.cmd(COMPILER,'check-selection',ccore,selection);chosen=self.q/'capture-selected.core.json';self.cmd(COMPILER,'emit-core',csrc,'--selection',selection,'-o',chosen)
  args=self.q/'capture.args.json';args.write_text(json.dumps([[0,7,4294967295,3],[5,2,8],7,4294967293])+'\n');a=json.loads(self.cmd(COMPILER,'run',ccore,'capture',args,'--core').stdout);b=json.loads(self.cmd(COMPILER,'run',chosen,'capture',args,'--core').stdout);self.assertEqual(a,b)
  (self.q/'false-controls.json').write_text(json.dumps(dict(rejected=results,distinct_outer_receiver_unmatched=True,curried_binder_shadowing_original_selected_equal=True,capture_result=a,counterexample=dict(xs=[2],ys=[5],h='a+b',g='v-x',aligned_left=[5],wrong_right=[2])),indent=2)+'\n')
if __name__=='__main__':unittest.main()
