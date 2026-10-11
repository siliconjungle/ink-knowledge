"""Complementary-partition identities, explicit callback instances and prior controls."""
import copy,hashlib,json,os,random,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.web_predicate19_laws import named_laws,source_functions,publish,specialize
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent
COMPILER=REPO.parent/'toolchain/ink-sequence-proofs'
PIN='44da9d5032f213c6458bbce156792a47187568aad56af44e3b5832993ede70a5'
BASELINE=ROOT/'store/snapshots'/f'{PIN}.json'
SHA='45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08'


def wrap(t,x):
 bits=64 if t=='u64' else 32;x&=(1<<bits)-1
 return x-(1<<bits) if t=='i32' and x>=1<<(bits-1) else x


def frames(t):
 lo,hi=(-(1<<31),(1<<31)-1) if t=='i32' else (0,(1<<(64 if t=='u64' else 32))-1)
 rng=random.Random(190)
 return [([],hi,hi),([lo,0,1,hi],7,7),([lo,hi],hi,wrap(t,-3)),([0,1,hi],lo,0),([lo,hi,1],hi,1),([0,0,1,1],1,hi),([rng.randint(lo,hi) for _ in range(17)],7,hi-2),([rng.randint(lo,hi) for _ in range(31)],hi,7)]


def oracle(name,args,heldout):
 t=name.removesuffix('_heldout').rsplit('_',1)[1];xs,seed,k=args;w=lambda x:wrap(t,x)
 p=lambda x:x>seed if heldout else x<seed
 literal_f=lambda x:w((w(k-x) if x<k else w(x-k))+seed) if heldout else w(w(x+7)*w(x+seed))
 math_f=lambda x:(k-x if x<k else x-k)+seed if heldout else (x+7)*(x+seed)
 # Faithful eager source: finish the first filter/map/sum before the second.
 positive=[literal_f(x) for x in [x for x in xs if p(x)]]
 a=0
 for y in positive:a=w(a+y)
 negative=[literal_f(x) for x in [x for x in xs if not p(x)]]
 b=0
 for y in negative:b=w(b+y)
 literal=w(w(a*k)+w(b*3)) if 'weighted' in name else w(a-b) if 'contrast' in name else w(a+b)
 # Independent unbounded algebra, one final modulo, with original-value branch.
 total=0
 for x in xs:total+=math_f(x)*(k if p(x) else 3) if 'weighted' in name else math_f(x)*(1 if p(x) else -1) if 'contrast' in name else math_f(x)
 return literal,w(total)


def alpha(l):
 names={}
 def walk(v):
  if isinstance(v,dict):
   if 'Free' in v:n=v['Free'];names.setdefault(n,'v'+str(len(names)));return {'Free':names[n]}
   return {k:walk(v[k]) for k in sorted(v)}
  if isinstance(v,list):return [walk(x) for x in v]
  return v
 return canonical([walk(l['from']),walk(l['to']),walk(l.get('conditions',[]))])


class Predicate19Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];archive=os.environ.get('INK_PREDICATE19_EVIDENCE')
  if archive:self.q=Path(archive).resolve()/self._testMethodName;self.q.mkdir(parents=True,exist_ok=True)
  else:self.temp=tempfile.TemporaryDirectory();self.q=Path(self.temp.name)
 def tearDown(self):
  if os.environ.get('INK_PREDICATE19_EVIDENCE'):(self.q/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.temp.cleanup()
 def cmd(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=r.args,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def source(self,functions,label):
  source=self.q/(label+'.ink');core=self.q/(label+'.core.json');source.write_text('module Predicate19;\n'+'\n'.join(s for _,s in functions)+'\n');self.cmd(COMPILER,'emit-core',source,'-o',core);return source,core
 def test_nine_alpha_fresh_generic_partition_endpoints(self):
  laws=named_laws();ids=[identity(semantic_entry(l)) for _,l in laws];self.assertEqual(len(set(ids)),9)
  prior=Store(ROOT,BASELINE);self.assertEqual(len(prior.members()),1298);self.assertFalse(set(ids)&set(prior.members()));endpoints={alpha(l) for _,l in laws}
  self.assertEqual(len(endpoints),9)
  for i in prior.members():
   p=prior.object(i)['payload']
   if 'from' in p and 'to' in p:self.assertNotIn(alpha(p),endpoints)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_typed_admission_default_prior_selection_replay_and_144_frames(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA)
  planner=REPO/'planner/ink_planner/semantic_search.py';ph=hashlib.sha256(planner.read_bytes()).hexdigest();prior=Store(ROOT,BASELINE)
  all_static=[];subjects={}
  for heldout in (False,True):
   _,core=self.source(source_functions(heldout),'all-'+str(heldout));subject=self.q/('subject-'+str(heldout)+'.json');self.cmd(COMPILER,'emit-semantic',core,'--core','-o',subject);subjects[heldout]=json.loads(subject.read_text());all_static+=specialize(subjects[heldout])
  self.assertEqual(len(all_static),18);named=named_laws()+all_static;objects={identity(semantic_entry(l)):semantic_entry(l) for _,l in named};self.assertEqual(len(objects),27)
  st=Store.publish(self.q/'candidate-store',list(objects.values()));view=self.q/'all.view.json';view.write_bytes(canonical(st.bundle(list(objects)))+b'\n');receipt=json.loads(self.cmd(COMPILER,'knowledge-check',self.q/'all-False.core.json',view).stdout);self.assertEqual(set(receipt['entries']),set(objects))
  (self.q/'static-certificates.json').write_text(json.dumps([dict(name=n,id=identity(semantic_entry(l)),law=l) for n,l in all_static],indent=2)+'\n')
  frames_done=[];plans=[]
  for heldout in (False,True):
   functions=source_functions(heldout)
   for index in (0,3,6):
    group=functions[index:index+3];label=('heldout' if heldout else 'primary')+'-'+str(index);source,core=self.source(group,label);selected={};packages={}
    for kind,store,snapshot in [('prior1298',prior,BASELINE),('candidate27',st,st.data/'snapshot.json')]:
     path=self.q/(label+'-'+kind+'.selection.json');self.cmd(sys.executable,REPO/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',store.root,'--snapshot',snapshot,'--budget',4096,'--compact-output','-o',path)
     pkg=json.loads(path.read_text());packages[kind]=pkg;self.cmd(COMPILER,'check-selection',core,path);out=self.q/(label+'-'+kind+'.selected.core.json');self.cmd(COMPILER,'emit-core',source,'--selection',path,'-o',out);selected[kind]={f['name']:f['body'] for f in json.loads(out.read_text())['program']['functions']};plans.append(dict(label=label,catalogue=kind,applications=pkg['applications'],scope='Candidate27 minimal catalogue; root full-union integration supplies symmetric old-only callback certificates before timings.'))
    for name,_ in group:
     apps=[a for a in packages['candidate27']['applications'] if a['function']==name];self.assertEqual(len(apps),1);self.assertTrue(objects[apps[0]['law']]['dependencies']);self.assertNotEqual(selected['candidate27'][name],selected['prior1298'][name])
     for i,args in enumerate(frames(name.removesuffix('_heldout').rsplit('_',1)[1])):
      path=self.q/(label+'-'+name+'-'+str(i)+'.args.json');path.write_text(json.dumps(args)+'\n');literal,expected=oracle(name,args,heldout);self.assertEqual(literal,expected)
      original=json.loads(self.cmd(COMPILER,'run',source,name,path).stdout);changed=json.loads(self.cmd(COMPILER,'run',source,name,path,'--selection',self.q/(label+'-candidate27.selection.json')).stdout);self.assertEqual(original,expected);self.assertEqual(changed,expected);frames_done.append(dict(name=name,heldout=heldout,args=args,original=original,selected=changed,oracle=expected))
  self.assertEqual(len(frames_done),144);(self.q/'interpreter-results.json').write_text(json.dumps(frames_done,indent=2)+'\n');(self.q/'selection-comparison.json').write_text(json.dumps(plans,indent=2)+'\n');self.assertEqual(hashlib.sha256(planner.read_bytes()).hexdigest(),ph)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_three_hash_valid_semantically_false_endpoints(self):
  _,core=self.source(source_functions(t='u32'),'negative')
  for name,l in named_laws()[:3]:
   bad=copy.deepcopy(l);bad['to']={'sort':l['to']['sort'],'node':{'Word':0}};o=semantic_entry(bad);st=Store.publish(self.q/name,[o]);v=self.q/(name+'.view.json');v.write_bytes(canonical(st.bundle([identity(o)]))+b'\n');r=self.cmd(COMPILER,'knowledge-check',core,v,success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_callback_stage_correlation_is_checked_not_assumed(self):
  _,core=self.source(source_functions(t='u32'),'correlation');subject=self.q/'subject.json';self.cmd(COMPILER,'emit-semantic',core,'--core','-o',subject);s=json.loads(subject.read_text());name='partition_recombine_u32';body=s['functions'][name]
  # Change negative mapper to identity: extraction from positive stage remains
  # the same, but the complete Normalize bridge must reject the mismatch.
  negative=body['node']['Op'][1][1]['node']['Op'][1][0];negative['node']['Op'][1][1]['node']['Lambda']={'sort':{'Value':'U32'},'node':{'Bound':0}}
  rows=specialize(dict(functions={name:body}));self.assertEqual(len(rows),1);st=Store.publish(self.q/'false-correlation',[semantic_entry(l) for _,l in named_laws()+rows]);v=self.q/'false-correlation.view.json';v.write_bytes(canonical(st.bundle([identity(semantic_entry(rows[0][1]))]))+b'\n');r=self.cmd(COMPILER,'knowledge-check',core,v,success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr)
if __name__=='__main__':unittest.main()
