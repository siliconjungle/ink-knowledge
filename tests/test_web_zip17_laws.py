"""Independent-list zip proofs: checked induction, source reuse and truncation."""
import copy,hashlib,json,math,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.beta_specialization15 import derive
from producers.web_zip17_laws import grouped_laws,named_laws,publish,source_functions,specialize
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent
COMPILER=REPO.parent/'toolchain/ink-sequence-proofs'
PIN='cc8308b40f651cdc3e5ece5b32ea94cea81bc2596046680384138fa16dd8ed9a'
BASELINE=ROOT/'store/snapshots'/f'{PIN}.json'
SHA='45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08'
def alpha(l):
 names={}
 def walk(v):
  if isinstance(v,dict):
   if set(v)=={'Free'}:names.setdefault(v['Free'],'v'+str(len(names)));return {'Free':names[v['Free']]}
   return {k:walk(v[k]) for k in sorted(v)}
  if isinstance(v,list):return [walk(x) for x in v]
  return v
 return canonical(walk([l['from'],l['to'],l.get('conditions',[])]))
def decode(x):return struct.unpack('<f',struct.pack('<I',x['F32Bits']))[0] if isinstance(x,dict) else x
def normalize(x,t):
 if t=='f32':
  try:return struct.unpack('<f',struct.pack('<f',x))[0]
  except OverflowError:return math.copysign(math.inf,x)
 bits=64 if t=='u64' else 32;x&=(1<<bits)-1
 return x-(1<<bits) if t=='i32' and x>=1<<(bits-1) else x
def key(x,t):return struct.unpack('<I',struct.pack('<f',decode(x)))[0] if t=='f32' else x
def oracle(name,args,heldout,eager):
 """Eager complete maps versus independently indexed truncated scalar work."""
 t=name.rsplit('_',1)[1];family=name.split('_')[1];xs,ys,seed,k=args
 xs,ys=[decode(x) for x in xs],[decode(y) for y in ys];seed,k=decode(seed),decode(k);w=lambda x:normalize(x,t)
 def left(x):
  if family not in ('left','both'):return x
  if heldout:return w(seed-x) if x<seed else w(x-seed)
  return w(w(x*3)+seed)
 def right(y):return (w(w(y*y)+k) if heldout else w(y+k)) if family in ('right','both') else y
 def combine(a,b):return (w(a+w(b*k)) if a<seed else w(a-b)) if heldout else w(a-w(b*k))
 def post(z):return w(w(z*k)+seed) if heldout else w(z+seed)
 if eager:
  a=[left(x) for x in xs];b=[right(y) for y in ys];z=[combine(x,y) for x,y in zip(a,b)];return [post(v) for v in z]
 return [post(combine(left(xs[i]),right(ys[i]))) for i in range(min(len(xs),len(ys)))]
def frames(t):
 if t=='f32':
  edge=[0.0,-0.0,1.5,-2.0,65536.0,{'F32Bits':0x7fc00000},{'F32Bits':0x7f800000},{'F32Bits':0xff800000}];seed,k=0.25,-2.0
 else:
  bits=64 if t=='u64' else 32;w=lambda x:normalize(x,t);edge=[w(x) for x in [0,1,2,(1<<(bits-1)),(1<<bits)-1]];seed,k=w(7),w(-3)
 rows=[[[],[],seed,k],[[],edge,seed,k],[edge,[],seed,k],[edge,edge[:2],seed,k],[edge[:2],edge,seed,k],[edge,list(reversed(edge)),seed,k],[edge,edge,normalize(0,t),normalize(1,t)]]
 rng=random.Random(170)
 for nx,ny in [(17,31),(31,17)]:
  number=(lambda: rng.randint(-4096,4096)/16) if t=='f32' else (lambda: normalize(rng.getrandbits(64 if t=='u64' else 32),t))
  rows.append([[number() for _ in range(nx)],[number() for _ in range(ny)],number(),number()])
 if t=='f32':rows.extend([[edge,edge,-0.0,{'F32Bits':0x7fc00000}],[edge,edge,{'F32Bits':0x7fc00000},-0.0]])
 return rows
class Zip17Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];archive=os.environ.get('INK_ZIP17_EVIDENCE')
  if archive:self.q=Path(archive).resolve()/self._testMethodName;self.q.mkdir(parents=True,exist_ok=True)
  else:self.tmp=tempfile.TemporaryDirectory();self.q=Path(self.tmp.name)
 def tearDown(self):
  if os.environ.get('INK_ZIP17_EVIDENCE'):(self.q/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def run_command(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(command=r.args,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def source(self,functions,label):
  s=self.q/(label+'.ink');c=self.q/(label+'.core.json');s.write_text('module Zip17;\n'+'\n'.join(v for _,v in functions)+'\n');self.run_command(COMPILER,'emit-core',s,'-o',c);return s,c
 def assert_values(self,actual,expected,t):
  self.assertEqual(len(actual),len(expected))
  for x,y in zip(actual,expected):
   if t=='f32' and math.isnan(decode(y)):self.assertTrue(math.isnan(decode(x)))
   else:self.assertEqual(key(x,t),key(y,t))
 def test_12_fusion_and_12_support_endpoints_alpha_fresh_against_1164(self):
  support,fusion=grouped_laws();self.assertEqual((len(support),len(fusion)),(12,12));ids={identity(semantic_entry(l)) for _,l in named_laws()};self.assertEqual(len(ids),24);old=Store(ROOT,BASELINE);self.assertEqual(len(old.members()),1164);self.assertFalse(ids&set(old.members()));endpoints={alpha(l) for _,l in named_laws()};self.assertEqual(len(endpoints),24)
  for i in old.members():
   p=old.object(i)['payload']
   if 'from' in p and 'to' in p:self.assertNotIn(alpha(p),endpoints)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_admission_default_selection_replay_reification_and_typed_independent_frames(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA);planner=REPO/'planner/ink_planner/semantic_search.py';ph=hashlib.sha256(planner.read_bytes()).hexdigest();old=Store(ROOT,BASELINE);support,fusion=grouped_laws();all_static=[]
  for heldout in (False,True):
   _,core=self.source(source_functions(heldout),'all-'+str(heldout));sp=self.q/('all-'+str(heldout)+'.subject.json');self.run_command(COMPILER,'emit-semantic',core,'--core','-o',sp);rows=specialize(json.loads(sp.read_text()));self.assertEqual(len(rows),12);all_static+=rows
  objects={identity(semantic_entry(l)):semantic_entry(l) for _,l in named_laws()+all_static};self.assertEqual(len(objects),48);candidate=Store.publish(self.q/'candidate-store',list(objects.values()));candidate.rebuild();view=self.q/'candidate-view.json';view.write_bytes(canonical(candidate.bundle(sorted(objects)))+b'\n');admission=json.loads(self.run_command(COMPILER,'knowledge-check',self.q/'all-False.core.json',view).stdout);self.assertEqual(set(admission['entries']),set(objects));(self.q/'admission.json').write_text(json.dumps(admission,indent=2)+'\n');(self.q/'static-certificates.json').write_text(json.dumps([dict(name=n,id=identity(semantic_entry(l)),law=l) for n,l in all_static],indent=2)+'\n')
  records=[];plans=[]
  for heldout in (False,True):
   functions=source_functions(heldout)
   for i in range(0,12,3):
    group=functions[i:i+3];label=str(heldout)+'-'+str(i);source,core=self.source(group,label);original={f['name']:f['body'] for f in json.loads(core.read_text())['program']['functions']};selected={};packages={}
    for kind,st in [('prior1164',old),('candidate48',candidate)]:
     with tempfile.TemporaryDirectory(prefix='zip17-plan-') as td:
      full=Path(td)/'selection.json';r=self.run_command(sys.executable,REPO/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',st.root,'--snapshot',BASELINE if kind=='prior1164' else st.data/'snapshot.json','--budget',4096,'-o',full);search=json.loads(r.stdout);self.assertFalse(search['exhausted']);p=json.loads(full.read_text());fullsha=hashlib.sha256(full.read_bytes()).hexdigest();used=sorted({a['law'] for a in p['applications']});p['knowledge']=st.bundle(used)
     package=self.q/(label+'-'+kind+'.selection.json');package.write_bytes(canonical(p)+b'\n');packages[kind]=p;self.run_command(COMPILER,'check-selection',core,package);out=self.q/(label+'-'+kind+'.selected.core.json');self.run_command(COMPILER,'emit-core',source,'--selection',package,'-o',out);selected[kind]={f['name']:f['body'] for f in json.loads(out.read_text())['program']['functions']};plans.append(dict(label=label,catalogue=kind,search=search,full_selection_sha256=fullsha,applications=p['applications'],scope='Minimal candidate48, not parent full-union parity catalogue; parent supplies symmetric old-only support.'))
    for name,_ in group:
     apps=[a for a in packages['candidate48']['applications'] if a['function']==name];self.assertEqual(len(apps),1);self.assertTrue(set(objects[apps[0]['law']]['dependencies'])&{identity(semantic_entry(l)) for _,l in fusion});self.assertEqual(selected['prior1164'][name],original[name]);self.assertNotEqual(selected['candidate48'][name],selected['prior1164'][name]);t=name.rsplit('_',1)[1]
     for fi,args in enumerate(frames(t)):
      eager=oracle(name,args,heldout,True);fused=oracle(name,args,heldout,False);self.assert_values(fused,eager,t);arg=self.q/(label+'-'+str(fi)+'.args.json');arg.write_text(json.dumps(args)+'\n');a=json.loads(self.run_command(COMPILER,'run',source,name,arg).stdout);b=json.loads(self.run_command(COMPILER,'run',source,name,arg,'--selection',self.q/(label+'-candidate48.selection.json')).stdout);self.assert_values(a,eager,t);self.assert_values(b,eager,t);self.assertEqual([key(x,t) for x in a],[key(x,t) for x in b]);records.append(dict(name=name,heldout=heldout,args=args,original=a,selected=b,expected=[{'F32Bits':key(x,t)} if t=='f32' else x for x in eager]))
  (self.q/'selection-comparison.json').write_text(json.dumps(plans,indent=2)+'\n');(self.q/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');self.assertEqual(hashlib.sha256(planner.read_bytes()).hexdigest(),ph);self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_three_hash_valid_wrong_zip_callbacks_are_rejected(self):
  _,core=self.source(source_functions()[:3],'false');support,fusion=grouped_laws();supportobjects={identity(semantic_entry(l)):semantic_entry(l) for _,l in support}
  for name,l in fusion[:3]:
   bad=copy.deepcopy(l);# Drop postmapper from target only: true proof bytes no longer establish endpoint.
   zipper=bad['to']['node']['Op'][1][2];body=zipper['node']['Lambda']['node']['Lambda'];zipper['node']['Lambda']['node']['Lambda']=body['node']['Op'][1][1];obj=semantic_entry(bad);objects=[supportobjects[d] for d in obj['dependencies']]+[obj];st=Store.publish(self.q/name,objects);view=self.q/(name+'.view.json');view.write_bytes(canonical(st.bundle([identity(obj)]))+b'\n');r=self.run_command(COMPILER,'knowledge-check',core,view,success=False);self.assertNotEqual(r.returncode,0);self.assertNotIn('identity mismatch',r.stderr);self.assertTrue(any(s in r.stderr for s in ['semantic normal forms differ','condition does not establish goal','law does not match exact application endpoints']))
if __name__=='__main__':unittest.main()
