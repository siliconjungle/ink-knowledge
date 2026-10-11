"""Checked composed partition sums and independent CPU/GPU deployments."""
import copy,hashlib,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import word
from producers.web_gpu21_laws import named_laws,publish,source_functions,specialize,mapped_sum_laws
from producers.web_predicate21_laws import named_laws as cpu_laws,specialize as cpu_specialize
from test_web_predicate21_laws import frames,literal,mathematical,alpha
ROOT=Path(__file__).resolve().parents[1]
COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs'
PIN='1846f49f86f1451f7e4a21406ff48327691563f0bb36787925439d348c41da91'
REPORT=ROOT.parent/'reports/web-stack-proofs-21-2026-10-11'
ZIG=ROOT.parent.parent/'toolchain/zig-aarch64-macos-0.15.2/zig'
class Gpu21Tests(unittest.TestCase):
 def setUp(self):
  self.commands=[];self.archive=os.environ.get('INK_GPU21_EVIDENCE')
  if self.archive:self.directory=Path(self.archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
  else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-gpu21-');self.directory=Path(self.tmp.name)
 def tearDown(self):
  if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
  else:self.tmp.cleanup()
 def command(self,*args,success=True):
  r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
  if success:self.assertEqual(r.returncode,0,r.stderr)
  return r
 def test_composed_endpoints_dependencies_and_novelty(self):
  old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');rows=named_laws();ids={identity(semantic_entry(l)) for _,l in rows};self.assertEqual(len(ids),9);self.assertFalse(ids&set(old.members()));endpoints={alpha(l) for _,l in rows}
  for oid in old.members():
   p=old.object(oid)['payload']
   if isinstance(p.get('from'),dict) and 'node' in p['from']:self.assertNotIn(alpha(p),endpoints)
  self.assertTrue(all(identity(semantic_entry(l)) in old.members() for _,l in mapped_sum_laws()));self.assertTrue(all(len(l['dependencies'])==2 and not l['conditions'] for _,l in rows))
  (self.directory/'scope.json').write_text(json.dumps(dict(baseline=PIN,composed_generic_endpoints=9,new_primitive_mathematics=0,names={n:identity(semantic_entry(l)) for n,l in rows}),indent=2)+'\n')
 def test_two_policies_replay_typed_values_and_real_gpu_bundles(self):
  self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
  rows=source_functions()+source_functions(True);src=self.directory/'typed.ink';src.write_text('module TypedGpu21;\n'+'\n'.join(text for _,text in rows)+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');self.command(COMPILER,'emit-core',src,'-o',core);self.command(COMPILER,'emit-semantic',core,'--core','-o',sem);subject=json.loads(sem.read_text());gpu_static=specialize(subject);cpu_static=cpu_specialize(subject);self.assertEqual(len(gpu_static),18);self.assertEqual(len(cpu_static),18);st=publish(self.directory/'isolated',cpu_static+gpu_static);self.assertEqual(len(st.members()),57);admission=self.command(COMPILER,'knowledge-check',core,st.root/'view.json');selected={};after={};searches=[]
  for policy in ('cpu','gpu'):
   apps=[]
   for heldout in (False,True):
    for t in ('u32','i32','u64'):
     group=source_functions(heldout,t);unit=self.directory/f'{policy}-{t}-{int(heldout)}.ink';unit.write_text('module UnitGpu21;\n'+'\n'.join(text for _,text in group)+'\n');uc=unit.with_suffix('.core.json');selection=unit.with_suffix('.selection.json');self.command(COMPILER,'emit-core',unit,'-o',uc);r=self.command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',REPORT/f'{policy}-cost-model.json','--budget',4096,'--compact-output','-o',selection);search=json.loads(r.stdout);searches.append(dict(policy=policy,type=t,heldout=heldout,search=search));self.assertFalse(search['exhausted']);part=json.loads(selection.read_text());self.assertEqual(len(part['applications']),3);apps+=part['applications'];self.command(COMPILER,'check-selection',uc,selection)
     if policy=='gpu' and t=='u32':
      sc=unit.with_suffix('.selected.core.json');self.command(COMPILER,'emit-core',unit,'--selection',selection,'-o',sc);bundle=self.directory/f'gpu-u32-{int(heldout)}-bundle';self.command(COMPILER,'build',sc,'--core','--target','webgpu','--zig',ZIG,'-o',bundle);manifest=json.loads((bundle/'manifest.json').read_text());self.assertEqual(len(manifest['functions']),3)
      for fn in manifest['functions']:
       self.assertIsNone(fn.get('shader'));self.assertEqual(fn.get('fallback_reason'),'GPU v2 currently requires an array result; ordered scalar reductions use CPU')
      self.assertEqual(manifest['schema'],2)
   combined=self.directory/f'{policy}.selection.json';combined.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');self.command(COMPILER,'check-selection',core,combined);selected[policy]=self.directory/f'{policy}.core.json';ssem=self.directory/f'{policy}.semantic.json';self.command(COMPILER,'emit-core',src,'--selection',combined,'-o',selected[policy]);self.command(COMPILER,'emit-semantic',selected[policy],'--core','-o',ssem);after[policy]=json.loads(ssem.read_text())['functions']
  records=[]
  for name,_ in rows:
   c=json.dumps(after['cpu'][name]);g=json.dumps(after['gpu'][name]);self.assertEqual(c.count('call:foldr'),1);self.assertNotIn('method:map',c);self.assertNotIn('method:filter',c);self.assertNotIn('call:sum',c);self.assertEqual(g.count('call:sum'),1);self.assertEqual(g.count('method:map'),1);self.assertNotIn('call:foldr',g);self.assertNotIn('method:filter',g);heldout=name.endswith('_heldout');t=name.replace('_heldout','').rsplit('_',1)[1];family='weighted' if 'weighted' in name else 'subtract' if 'subtract' in name else 'add'
   for i,args in enumerate(frames(t)):
    path=self.directory/f'args-{t}-{i}.json';path.write_text(json.dumps(args)+'\n');expected=mathematical(args,t,heldout,family);self.assertEqual(literal(args,t,heldout,family),expected);values={'original':json.loads(self.command(COMPILER,'run',src,name,path).stdout)}
    for policy in ('cpu','gpu'):values[policy]=json.loads(self.command(COMPILER,'run',selected[policy],name,path,'--core').stdout)
    self.assertTrue(all(v==expected for v in values.values()));records.append(dict(function=name,arguments=args,expected=expected,values=values))
  # Authenticate the exact prepared corpus; indexed subjects are untouched by this bridge.
  corpus=[]
  for p in sorted((REPORT/'input-preparation').glob('*/input.semantic.json')):
   value=json.loads(p.read_text());certs=specialize(value);corpus.append(dict(path=str(p.relative_to(ROOT.parent)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),gpu_static_certificates=len(certs)))
   if 'partition_dual_' in p.parent.name:self.assertEqual(len(certs),1);self.assertIn(identity(semantic_entry(certs[0][1])),{identity(semantic_entry(v)) for _,v in gpu_static})
   else:self.assertEqual(len(certs),0)
  self.assertEqual(len(corpus),12);self.assertEqual(sum(v['gpu_static_certificates'] for v in corpus),6)
  (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(isolated_entries=57,composed_roots=9,typed_cpu_static=18,typed_gpu_static=18,frames=len(records),actual_interpreter_runs=3*len(records),real_u32_gpu_shaders=0,actual_u32_fallback_builds=6,gpu_calls_executed=0,corpus=corpus,admission=json.loads(admission.stdout),searches=searches),indent=2)+'\n')
 def test_hash_valid_false_compositions_reject(self):
  src=self.directory/'negative.ink';src.write_text('module FalseGpu21;\n'+source_functions(t='u32')[0][1]+'\n');core=src.with_suffix('.core.json');self.command(COMPILER,'emit-core',src,'-o',core);records=[]
  for family in ('add','weighted'):
   bad=copy.deepcopy(dict(named_laws())['partition_dual_'+family+'_u32_parallel_sum']);bad['to']=word('U32',1);bad['proof']='Normalize';st=publish(self.directory/family,[(family+'_false',bad)]);r=self.command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);records.append(dict(content_id=identity(semantic_entry(bad)),stderr=r.stderr))
  (self.directory/'false-controls.json').write_text(json.dumps(records,indent=2)+'\n')
if __name__=='__main__':unittest.main()
