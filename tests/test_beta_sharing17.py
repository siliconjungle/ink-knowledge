"""Shared static beta certificates: hygiene, execution and frozen policy costs."""
import copy,hashlib,json,math,os,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import value,var,bound,lam,binary,op
from producers.beta_specialization15 import beta_normalize,free_parameters
from producers.beta_sharing17 import beta_share,derive
from producers.web_zip17_laws import grouped_laws,source_functions as zip_sources
from producers.web_fold17_laws import named_laws as fold_laws,dependency_objects,source_functions as fold_sources
from tests.test_web_zip17_laws import frames as zip_frames,oracle as zip_oracle,key,decode
from tests.test_web_fold17_laws import frames as fold_frames,eager_oracle
from ink_planner.semantic_search import cost
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent;COMPILER=REPO.parent/'toolchain/ink-sequence-proofs';REPORT=REPO/'reports/web-stack-proofs-17-2026-10-10'
SHA='45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08'
def count_apply(t):
 if isinstance(t,dict):return int(isinstance(t.get('node'),dict) and t['node'].get('Op',[None])[0]=='apply')+sum(count_apply(v) for v in t.values())
 if isinstance(t,list):return sum(count_apply(v) for v in t)
 return 0
class Sharing17Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];a=os.environ.get('INK_SHARING17_EVIDENCE')
  if a:self.q=Path(a).resolve()/self._testMethodName;self.q.mkdir(parents=True,exist_ok=True)
  else:self.tmp=tempfile.TemporaryDirectory();self.q=Path(self.tmp.name)
 def tearDown(self):
  if os.environ.get('INK_SHARING17_EVIDENCE'):(self.q/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def run_command(self,*argv,success=True):
  r=subprocess.run(list(map(str,argv)),capture_output=True,text=True);self.commands.append(dict(command=r.args,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def test_curried_binder_hygiene_unknown_callback_and_idempotence(self):
  for t in ('U32','I32','U64','F32'):
   s=value(t);x=bound(s,0);k=var(s,'__beta_share_0');h=lam(s,lam(s,binary('+',binary('+',bound(s,1),bound(s,1)),bound(s,0))));arg=binary('*',x,k);call=op(s,'apply',op(h['sort']['Arrow'][1],'apply',h,arg),binary('-',x,k));subject=lam(s,call);shared=beta_share(subject)
   self.assertEqual(beta_normalize(shared),beta_normalize(subject));self.assertEqual(beta_share(shared),shared);self.assertEqual(free_parameters(shared),free_parameters(subject));self.assertEqual(count_apply(shared),1)
   unknown=op(s,'apply',var(lam(s,x)['sort'],'callback'),arg);self.assertEqual(beta_share(unknown),unknown)
   partial=op(h['sort']['Arrow'][1],'apply',h,arg);partial_result=beta_share(partial);self.assertIn('Lambda',partial_result['node']);self.assertEqual(beta_normalize(partial_result),beta_normalize(partial));self.assertEqual(count_apply(partial_result),0)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_checked_shared_all_typed_zip_fold_callbacks_reification_and_natural_policy(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA);planner=REPO/'planner/ink_planner/semantic_search.py';ph=hashlib.sha256(planner.read_bytes()).hexdigest();store=Store(ROOT);generic=grouped_laws()[1]+fold_laws();subjects={};sources={};all_rows=[]
  for alternate in (False,True):
   funcs=zip_sources(alternate)+fold_sources(alternate)
   for t in ('u32','i32','u64','f32'):
    label=str(alternate)+'-'+t;rows=[(n,s) for n,s in funcs if n.endswith('_'+t)];source=self.q/(label+'.ink');core=self.q/(label+'.core.json');source.write_text('module Sharing17;\n'+'\n'.join(s for _,s in rows)+'\n');self.run_command(COMPILER,'emit-core',source,'-o',core);sp=self.q/(label+'.subject.json');self.run_command(COMPILER,'emit-semantic',core,'--core','-o',sp);subject=json.loads(sp.read_text());subjects[label]=subject;sources[label]=(source,core,rows,alternate,t);derived=derive(subject,generic);all_rows+=derived
  objects={identity(semantic_entry(l)):semantic_entry(l) for _,l in all_rows}
  objects.update({identity(semantic_entry(l)):semantic_entry(l) for _,l in grouped_laws()[0]+generic})
  objects.update({identity(o):o for o in dependency_objects()})
  st=Store.publish(self.q/'candidate',list(objects.values()));st.rebuild();view=self.q/'view.json';view.write_bytes(canonical(st.bundle(sorted({identity(semantic_entry(l)) for _,l in all_rows})))+b'\n');admit=self.run_command(COMPILER,'knowledge-check',next(iter(sources.values()))[1],view);(self.q/'admission.json').write_text(admit.stdout);records=[];plans=[];costs=[]
  models={'default':None}
  for kind in ['cpu','gpu']:
   for version,folder in [('initial',REPORT/'initial-preparation'),('current',REPORT)]:models[version+'-'+kind]=json.loads((folder/(kind+'-cost-model.json')).read_text())['operation_costs']
  for name,l in all_rows:
   costs.append(dict(name=name,id=identity(semantic_entry(l)),source={k:cost(l['from'],v) for k,v in models.items()},target={k:cost(l['to'],v) for k,v in models.items()},sharing_bindings=count_apply(l['to'])))
  for label,(source,core,functions,alternate,t) in sources.items():
   selected={}
   for policy in ['cpu','gpu']:
    package=self.q/(label+'-'+policy+'.selection.json');r=self.run_command(sys.executable,REPO/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',REPORT/(policy+'-cost-model.json'),'--budget',4096,'-o',package);search=json.loads(r.stdout);self.assertFalse(search['exhausted']);p=json.loads(package.read_text());p['knowledge']=st.bundle(sorted({a['law'] for a in p['applications']}));package.write_bytes(canonical(p)+b'\n');self.run_command(COMPILER,'check-selection',core,package);out=self.q/(label+'-'+policy+'.selected.core.json');self.run_command(COMPILER,'emit-core',source,'--selection',package,'-o',out);selected[policy]={f['name']:f['body'] for f in json.loads(out.read_text())['program']['functions']};plans.append(dict(label=label,policy=policy,search=search,applications=p['applications']))
    for name,_ in functions:
     if policy=='cpu' or name.startswith('independent_'):
      self.assertTrue(any(a['function']==name for a in p['applications']),name);self.assertNotEqual(selected[policy][name],json.loads(core.read_text())['program']['functions'][[n for n,_ in functions].index(name)]['body'])
   for name,_ in functions:
    frames=zip_frames(t) if name.startswith('independent_') else fold_frames(t)
    for i,args in enumerate(frames):
     expected=zip_oracle(name,args,alternate,True) if name.startswith('independent_') else eager_oracle(name,args,alternate)[0];arg=self.q/(label+'-'+name+'-'+str(i)+'.args.json');arg.write_text(json.dumps(args)+'\n');original=json.loads(self.run_command(COMPILER,'run',source,name,arg).stdout);changed=json.loads(self.run_command(COMPILER,'run',source,name,arg,'--selection',self.q/(label+'-cpu.selection.json')).stdout);xs=original if isinstance(original,list) else [original];ys=changed if isinstance(changed,list) else [changed];want=expected if isinstance(expected,list) else [expected];self.assertEqual([key(x,t) for x in xs],[key(y,t) for y in ys]);self.assertEqual(len(xs),len(want))
     for actual,oracle in zip(xs,want):
      if t=='f32' and math.isnan(decode(oracle)):self.assertTrue(math.isnan(decode(actual)))
      else:self.assertEqual(key(actual,t),key(oracle,t))
     records.append(dict(name=name,alternate=alternate,args=args,original=original,selected=changed))
  (self.q/'candidates.json').write_text(json.dumps([dict(name=n,id=identity(semantic_entry(l)),law=l) for n,l in all_rows],indent=2)+'\n');(self.q/'costs.json').write_text(json.dumps(costs,indent=2)+'\n');(self.q/'plans.json').write_text(json.dumps(plans,indent=2)+'\n');(self.q/'interpreter.json').write_text(json.dumps(records,indent=2)+'\n');self.assertEqual(hashlib.sha256(planner.read_bytes()).hexdigest(),ph);self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_hash_valid_wrong_shared_binding_is_semantically_rejected(self):
  name='independent_left_mapped_zip_postmap_u32_heldout';subject=json.loads((REPORT/'input-preparation'/name/'input.semantic.json').read_text());rows=derive(subject,grouped_laws()[1]);self.assertEqual(len(rows),1);candidate=copy.deepcopy(rows[0][1]);
  def corrupt(v):
   if isinstance(v,dict):
    n=v.get('node')
    if isinstance(n,dict) and n.get('Op',[None])[0]=='apply' and isinstance(n['Op'][1][0]['node'],dict) and 'Lambda' in n['Op'][1][0]['node']:
     n['Op'][1][1]=dict(sort=n['Op'][1][1]['sort'],node={'Word':1});return True
    return any(corrupt(x) for x in v.values())
   if isinstance(v,list):return any(corrupt(x) for x in v)
   return False
  self.assertTrue(corrupt(candidate['to']));obj=semantic_entry(candidate);objects={identity(semantic_entry(l)):semantic_entry(l) for _,l in grouped_laws()[0]+grouped_laws()[1]};objects[identity(obj)]=obj;st=Store.publish(self.q/'false',list(objects.values()));view=self.q/'false-view.json';view.write_bytes(canonical(st.bundle([identity(obj)]))+b'\n');r=self.run_command(COMPILER,'knowledge-check',REPORT/'input-preparation'/name/'input.core.json',view,success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr)
if __name__=='__main__':unittest.main()
