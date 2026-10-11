"""Conditional idempotence: general kernel, raw literal application and exact values."""
import copy,hashlib,json,os,math,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.web_idempotent18_laws import named_laws,publish,source_functions,grouped_laws
from producers.semantic_laws import value,var,bound,lam,op,nat,law
from ink_planner.semantic_search import substitute
from producers.beta_specialization15 import beta_normalize
from tests.test_web_zip17_laws import alpha,frames,decode,key
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parent;COMPILER=REPO.parent/'toolchain/ink-sequence-proofs';PIN='717bc5be3b6d186678d71d3c11ec5a10a0bdc884759993f1d70add7a37b20c76';BASE=ROOT/'store/snapshots'/f'{PIN}.json';MODEL=REPO/'reports/web-stack-proofs-17-2026-10-10/cpu-cost-model.json';SHA='45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08'
def oracle(name,args,alternate,count=1):
 xs,ys,seed,k=args;out=[]
 for original in xs:
  a=original
  for _ in range(count):
   if name.startswith('lower'):threshold=k if alternate else seed;a=threshold if decode(a)<decode(threshold) else a
   elif name.startswith('upper'):threshold=seed if alternate else k;a=threshold if decode(a)>decode(threshold) else a
   else:match=k if alternate else seed;replacement=seed if alternate else k;a=replacement if decode(a)==decode(match) else a
  out.append(a)
 return out
class Idempotent18Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];e=os.environ.get('INK_IDEMPOTENT18_EVIDENCE')
  if e:self.q=Path(e).resolve()/self._testMethodName;self.q.mkdir(parents=True,exist_ok=True)
  else:self.tmp=tempfile.TemporaryDirectory();self.q=Path(self.tmp.name)
 def tearDown(self):
  if os.environ.get('INK_IDEMPOTENT18_EVIDENCE'):(self.q/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def cmd(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),text=True,capture_output=True);self.commands.append(dict(command=r.args,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def source(self,rows,label):
  source=self.q/(label+'.ink');core=self.q/(label+'.core.json');source.write_text('module Idempotent18;\n'+'\n'.join(s for _,s in rows)+'\n');self.cmd(COMPILER,'emit-core',source,'-o',core);return source,core
 def values(self,a,b,t):self.assertEqual([key(x,t) for x in a],[key(x,t) for x in b])
 def test_roles_alpha_novelty_and_explicit_premises(self):
  old=Store(ROOT,BASE);rows=named_laws();ids={identity(semantic_entry(l)) for _,l in rows};self.assertEqual(len(ids),39);self.assertFalse(ids&set(old.members()));ends={alpha(l) for _,l in rows};self.assertEqual(len(ends),39)
  for i in old.members():
   payload=old.object(i)['payload']
   if 'from' in payload and 'node' in payload['from']:self.assertNotIn(alpha(payload),ends)
  support,function,scalar=grouped_laws();self.assertEqual(tuple(map(len,(support,function,scalar))),(5,5,5));self.assertTrue(all(len(l['conditions'])==1 for _,l in function+scalar));self.assertTrue(all(not l['conditions'] for _,l in support));(self.q/'novelty.json').write_text(json.dumps(dict(prior_entries=len(old.members()),prior_pin=PIN,ids=sorted(ids),alpha_endpoints=len(ends)))+'\n')
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_all_typed_admission_old_new_default_replay_and_interpreter(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),SHA);planner=REPO/'planner/ink_planner/semantic_search.py';ph=hashlib.sha256(planner.read_bytes()).hexdigest();st,manifest=publish(self.q/'candidate');allframes=[];plans=[]
  for alternate in (False,True):
   for t in ('u32','i32','u64','f32'):
    label=str(alternate)+'-'+t;rows=source_functions(alternate,t);source,core=self.source(rows,label)
    if not plans:self.cmd(COMPILER,'knowledge-check',core,st.root/'view.json')
    original=json.loads(core.read_text())['program']['functions'];selected={}
    for variant,store,snapshot in [('prior',Store(ROOT,BASE),BASE),('current',st,st.data/'snapshot.json')]:
     out=self.q/(label+'-'+variant+'.selection.json');result=self.cmd(sys.executable,REPO/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',store.root,'--snapshot',snapshot,'--cost-model',MODEL,'--compact-output','--budget',4096,'-o',out);search=json.loads(result.stdout);self.assertFalse(search['exhausted']);package=json.loads(out.read_text());self.cmd(COMPILER,'check-selection',core,out);dest=self.q/(label+'-'+variant+'.selected.core.json');self.cmd(COMPILER,'emit-core',source,'--selection',out,'-o',dest);selected[variant]=json.loads(dest.read_text())['program']['functions'];self.assertEqual(len(package['applications']),0 if variant=='prior' else 3);plans.append(dict(label=label,variant=variant,search=search,applications=package['applications']))
    self.assertEqual(selected['prior'],original);self.assertNotEqual(selected['current'],original)
    for name,_ in rows:
     count=8 if name.startswith('lower') else 32 if name.startswith('upper') else 64
     for i,args in enumerate(frames(t)):
      arg=self.q/(label+'-'+str(i)+'.args.json');arg.write_text(json.dumps(args)+'\n');literal=oracle(name,args,alternate,count);single=oracle(name,args,alternate,1);self.values(literal,single,t);a=json.loads(self.cmd(COMPILER,'run',source,name,arg).stdout);b=json.loads(self.cmd(COMPILER,'run',source,name,arg,'--selection',self.q/(label+'-current.selection.json')).stdout);self.values(a,b,t);self.values(a,literal,t);allframes.append(dict(name=name,type=t,alternate=alternate,args=args,literal=a,selected=b))
  (self.q/'interpreter.json').write_text(json.dumps(allframes,indent=2)+'\n');(self.q/'plans.json').write_text(json.dumps(plans,indent=2)+'\n');self.assertEqual(len(allframes),228);self.assertEqual(hashlib.sha256(planner.read_bytes()).hexdigest(),ph)
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_zero_one_counts_and_actual_bool_conditional_execution(self):
  records=[]
  for t in ('u32','i32','u64','f32'):
   for alternate in (False,True):
    for count in (0,1):
     rows=[(n,s.replace('repeat(8,',f'repeat({count},').replace('repeat(32,',f'repeat({count},').replace('repeat(64,',f'repeat({count},')) for n,s in source_functions(alternate,t)];label=f'{alternate}-{t}-{count}';source,core=self.source(rows,label)
     for name,_ in rows:
      for i in (0,3,5):
       args=frames(t)[i];arg=self.q/(label+'-'+str(i)+'.args.json');arg.write_text(json.dumps(args)+'\n');actual=json.loads(self.cmd(COMPILER,'run',source,name,arg).stdout);expected=oracle(name,args,alternate,count);self.values(actual,expected,t);records.append(dict(type=t,alternate=alternate,count=count,name=name,args=args,actual=actual))
  # Bool is a real executable repeat type. f(a)=choose(a,k,false)=a AND k.
  s=value('Bool');k=var(s,'k');x=var(s,'x');f=lam(s,op(s,'call:choose',bound(s,0),k,{'sort':s,'node':{'Bool':False}}));generic=dict(grouped_laws()[2])['idempotent_positive_repeat_bool'];boollaws=[]
  for count in (1,8,64):
   args={'n':nat(count-1),'x':x,'f':f};middle=substitute(generic['from'],args);result=substitute(generic['to'],args);source=op(s,'call:repeat',nat(count),x,lam(value('U32'),f));case={'Congruence':[{'Cases':dict(condition=var(s,'__congruence'),on_false='Normalize',on_true={'Cases':dict(condition=k,on_false='Normalize',on_true='Normalize')})}]};proof={'Trans':dict(middle=middle,left='Normalize',right={'Trans':dict(middle=result,left={'Use':dict(law=identity(semantic_entry(generic)),arguments=args,premises=[case])},right='Normalize')})};boollaws.append(law({'x':s,'k':s},source,beta_normalize(result),proof,dependencies=[identity(semantic_entry(generic))]))
  st=Store.publish(self.q/'bool-store',[semantic_entry(l) for _,l in named_laws()]+[semantic_entry(l) for l in boollaws]);st.rebuild();view=self.q/'bool-view.json';view.write_bytes(canonical(st.bundle([identity(semantic_entry(l)) for l in boollaws]))+b'\n');rows=[('bool'+str(n),f'pub fn bool{n}(xs:List<Bool>,k:Bool)->List<Bool>{{return xs.map(fn(x)=>repeat({n},x,fn(i)=>fn(a)=>choose(a,k,false)));}}') for n in (1,8,64)];source,core=self.source(rows,'bool');self.cmd(COMPILER,'knowledge-check',core,view);selection=self.q/'bool-selection.json';r=self.cmd(sys.executable,REPO/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',MODEL,'--compact-output','-o',selection);self.cmd(COMPILER,'check-selection',core,selection)
  for kvalue in (False,True):
   args=[[False,True,True,False],kvalue];arg=self.q/('bool-'+str(kvalue)+'.args.json');arg.write_text(json.dumps(args)+'\n')
   for name,_ in rows:
    a=json.loads(self.cmd(COMPILER,'run',source,name,arg).stdout);b=json.loads(self.cmd(COMPILER,'run',source,name,arg,'--selection',selection).stdout);self.assertEqual(a,b);self.assertEqual(a,[x and kvalue for x in args[0]]);records.append(dict(name=name,args=args,literal=a,selected=b))
  (self.q/'zero-one-bool.json').write_text(json.dumps(records,indent=2)+'\n')
 @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
 def test_hash_valid_false_endpoint_premise_and_zero_count_rejected(self):
  rows=named_laws();named=dict(rows);source,core=self.source(source_functions(),'false');objects={identity(semantic_entry(l)):semantic_entry(l) for _,l in rows};controls=[]
  for name in ('projection_repeat_lower_u32','projection_idempotence_lower_u32','idempotent_positive_repeat_u32'):
   wrong=copy.deepcopy(named[name])
   if name.startswith('projection_repeat_'):wrong['to']=var(value('U32'),'x')
   elif name.startswith('projection_idempotence_'):wrong['to']=lam(value('U32'),bound(value('U32'),0))
   else:wrong['from']['node']['Op'][1][0]=var('Nat','n')
   obj=semantic_entry(wrong);data=dict(objects);data[identity(obj)]=obj;st=Store.publish(self.q/name,list(data.values()));view=self.q/(name+'.view.json');view.write_bytes(canonical(st.bundle([identity(obj)]))+b'\n');r=self.cmd(COMPILER,'knowledge-check',core,view,success=False);self.assertNotEqual(r.returncode,0);self.assertNotIn('identity mismatch',r.stderr);self.assertTrue(any(x in r.stderr for x in ['semantic normal forms differ','law does not match exact application endpoints']));controls.append(dict(name=name,id=identity(obj),stderr=r.stderr))
  (self.q/'false-controls.json').write_text(json.dumps(controls,indent=2)+'\n')
if __name__=='__main__':unittest.main()
