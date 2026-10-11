"""Minimal views: generic weight sinking, explicit certificates, and old controls."""
import copy,hashlib,json,os,random,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.web_reduction16_laws import named_laws,source_functions,specialize
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent
COMPILER=REPO.parent/'toolchain/ink-sequence-proofs'
BASELINE=ROOT/'store/snapshots/57bbee1835725fd3af939cf11e3dda25ac51e12001fde0f006aeb64bb9ab2378.json'
SHA='45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08'
def wrap(t,x):
 bits=64 if t=='u64' else 32;x&=(1<<bits)-1
 return x-(1<<bits) if t=='i32' and x>=1<<(bits-1) else x
def frames(t):
 lo,hi=(-(1<<31),(1<<31)-1) if t=='i32' else (0,(1<<(64 if t=='u64' else 32))-1)
 rng=random.Random(16)
 return [([],hi,hi),([lo,0,1,hi],7,7),([lo,hi],hi,-3 if t=='i32' else hi-2),([0,1,hi],0,0),([lo,hi,1],1,1),([rng.randint(lo,hi) for _ in range(17)],7,hi-2),([rng.randint(lo,hi) for _ in range(31)],hi,7)]
def expected(name,xs,seed,k,heldout):
 t=name.rsplit('_',1)[1];w=lambda x:wrap(t,x)
 def literal_f(x):return w(w(x*x)+seed) if heldout else w(seed-x) if x<seed else w(x-seed)
 def math_f(x):return x*x+seed if heldout else abs(x-seed)
 values=[];mathematical=0
 for x in xs:
  if name.startswith('masked') and not (x>k if heldout else x<seed):values.append(0);continue
  first=w(literal_f(x)*k);second=w(literal_f(x)*seed)
  sign=-1 if 'subtract' in name else 1
  values.append(w(first+sign*second));mathematical+=math_f(x)*(k+sign*seed)
 acc=0
 for v in values:acc=w(acc+v)
 return acc,w(mathematical)
def alpha_endpoint(l):
 names={}
 def go(v):
  if isinstance(v,dict):
   if 'Free' in v:n=v['Free'];names.setdefault(n,'v'+str(len(names)));return {'Free':names[n]}
   return {k:go(v[k]) for k in sorted(v)}
  if isinstance(v,list):return [go(x) for x in v]
  return v
 return canonical([go(l['from']),go(l['to']),go(l.get('conditions',[]))])
class Reduction16Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];archive=os.environ.get('INK_REDUCTION16_EVIDENCE')
  if archive:self.q=Path(archive).resolve()/self._testMethodName;self.q.mkdir(parents=True,exist_ok=True)
  else:self.temp=tempfile.TemporaryDirectory();self.q=Path(self.temp.name)
 def tearDown(self):
  if os.environ.get('INK_REDUCTION16_EVIDENCE'):(self.q/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.temp.cleanup()
 def run_cmd(self,*argv,success=True):
  r=subprocess.run(list(map(str,argv)),capture_output=True,text=True);self.commands.append(dict(argv=r.args,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def source(self,functions,label):
  source=self.q/(label+'.ink');core=self.q/(label+'.core.json');source.write_text('module Reduction16;\n'+'\n'.join(s for _,s in functions)+'\n');self.run_cmd(COMPILER,'emit-core',source,'-o',core);return source,core
 def test_nine_generic_endpoints_are_alpha_fresh_in_prior1089(self):
  laws=named_laws();ids=[identity(semantic_entry(l)) for _,l in laws];self.assertEqual(len(set(ids)),9)
  old=Store(ROOT,BASELINE);self.assertEqual(len(old.members()),1089);self.assertFalse(set(ids)&set(old.members()));new={alpha_endpoint(l) for _,l in laws}
  for i in old.members():
   p=old.object(i)['payload']
   if 'from' in p and 'to' in p:self.assertNotIn(alpha_endpoint(p),new)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_admission_static_default_selection_prior_replay_and_126_frames(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA)
  planner=REPO/'planner/ink_planner/semantic_search.py';ph=hashlib.sha256(planner.read_bytes()).hexdigest();old=Store(ROOT,BASELINE)
  all_special=[];subjects={}
  for heldout in (False,True):
   _,core=self.source(source_functions(heldout),'all-'+str(heldout));subject=self.q/('subject-'+str(heldout)+'.json');self.run_cmd(COMPILER,'emit-semantic',core,'--core','-o',subject);subjects[heldout]=json.loads(subject.read_text());all_special+=specialize(subjects[heldout])
  objects={identity(semantic_entry(l)):semantic_entry(l) for _,l in named_laws()+all_special};self.assertEqual(len(objects),27)
  store=Store.publish(self.q/'candidate-store',list(objects.values()));store.rebuild();roots=[identity(semantic_entry(l)) for _,l in all_special];view=self.q/'candidate-view.json';view.write_bytes(canonical(store.bundle(roots))+b'\n');self.run_cmd(COMPILER,'knowledge-check',self.q/'all-False.core.json',view)
  (self.q/'static-certificates.json').write_text(json.dumps([dict(name=n,id=identity(semantic_entry(l)),law=l) for n,l in all_special],indent=2)+'\n')
  rows=[];plans=[]
  for heldout in (False,True):
   functions=source_functions(heldout)
   for index in range(0,9,3):
    group=functions[index:index+3];label=('heldout' if heldout else 'discovery')+'-'+str(index);source,core=self.source(group,label);selected={};packages={}
    for kind,catalogue in [('prior1089',old),('candidate27',store)]:
     # Full prior is queried in a transient plan; only selected dependency closure is archived.
     with tempfile.TemporaryDirectory(prefix='reduction16-plan-') as td:
      full=Path(td)/'selection.json';self.run_cmd(sys.executable,REPO/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',catalogue.root,'--snapshot',BASELINE if kind=='prior1089' else store.data/'snapshot.json','--budget',4096,'-o',full)
      package=json.loads(full.read_text());rawhash=hashlib.sha256(full.read_bytes()).hexdigest();used=sorted({a['law'] for a in package['applications']});package['knowledge']=catalogue.bundle(used)
     path=self.q/(label+'-'+kind+'.selection.json');path.write_bytes(canonical(package)+b'\n');packages[kind]=package
     self.run_cmd(COMPILER,'check-selection',core,path);out=self.q/(label+'-'+kind+'.selected.core.json');self.run_cmd(COMPILER,'emit-core',source,'--selection',path,'-o',out);selected[kind]={f['name']:f['body'] for f in json.loads(out.read_text())['program']['functions']}
     plans.append(dict(source=label,catalogue=kind,full_search_package_sha256=rawhash,archived_selected_dependency_closure=True,applications=package['applications'],scope='Candidate27 is a minimal alternative catalogue, not a full old+new union. Parent integrates full union and old-only certificate parity before performance claims.'))
    for name,_ in group:
     apps=[a for a in packages['candidate27']['applications'] if a['function']==name];self.assertEqual(len(apps),1);self.assertTrue(objects[apps[0]['law']]['dependencies']);self.assertNotEqual(selected['candidate27'][name],selected['prior1089'][name])
     for fi,(xs,seed,k) in enumerate(frames(name.rsplit('_',1)[1])):
      args=self.q/(label+'-'+name+'-'+str(fi)+'.args.json');args.write_text(json.dumps([xs,seed,k])+'\n');literal,oracle=expected(name,xs,seed,k,heldout);self.assertEqual(literal,oracle)
      original=json.loads(self.run_cmd(COMPILER,'run',source,name,args).stdout);changed=json.loads(self.run_cmd(COMPILER,'run',source,name,args,'--selection',self.q/(label+'-candidate27.selection.json')).stdout);self.assertEqual(original,oracle);self.assertEqual(changed,oracle)
      rows.append(dict(name=name,heldout=heldout,args=[xs,seed,k],original=original,selected=changed,oracle=oracle))
  self.assertEqual(len(rows),126);(self.q/'interpreter-results.json').write_text(json.dumps(rows,indent=2)+'\n');(self.q/'selection-comparison.json').write_text(json.dumps(plans,indent=2)+'\n');self.assertEqual(hashlib.sha256(planner.read_bytes()).hexdigest(),ph);self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_three_rehashed_false_weights_fail_semantic_checker(self):
  _,core=self.source(source_functions()[:3],'negative')
  for name,l in named_laws()[:3]:
   bad=copy.deepcopy(l);factor=bad['to']['node']['Op'][1][1];factor['node']['Op'][0]='binary:+' if 'subtract' in name else 'binary:-';obj=semantic_entry(bad);st=Store.publish(self.q/name,[obj]);view=self.q/(name+'.view.json');view.write_bytes(canonical(st.bundle([identity(obj)]))+b'\n');r=self.run_cmd(COMPILER,'knowledge-check',core,view,success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr)
if __name__=='__main__':unittest.main()
