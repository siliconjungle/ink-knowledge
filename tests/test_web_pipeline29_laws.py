"""Checked cardinality erasure, typed helper contexts and preserved negatives."""
import copy,hashlib,json,math,random,struct,subprocess,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path[:0]=[str(ROOT/'knowledge'),str(ROOT/'planner')]
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import binary,law,nat,op,value,var,word
from producers.web_pipeline29_laws import named_laws,grouped_laws,law_roles,reference_laws,source_functions,specialize,publish
from producers.beta_sharing17 import derive
from producers.definition_context28 import bind
PIN='39d4be8c0283389cc8b1092ad8075ff36080885abad6d1d56bb74455e105b63e'
COMPILER=ROOT.parent/'toolchain/ink-web-engine-28';BASE=ROOT/'reports/web-stack-proofs-29-2026-10-11/pipeline'

def alpha(law_):
 names={}
 def walk(v):
  if isinstance(v,dict):
   if set(v)=={'Free'}:names.setdefault(v['Free'],str(len(names)));return dict(Free=names[v['Free']])
   return {k:walk(v[k]) for k in sorted(v)}
  if isinstance(v,list):return [walk(x) for x in v]
  return v
 return canonical(walk([law_['from'],law_['to']]))

def number(x):return struct.unpack('<f',struct.pack('<I',x['F32Bits']))[0] if isinstance(x,dict) else x

def rounded(x,t):
 if t=='f32':
  try:return struct.unpack('<f',struct.pack('<f',x))[0]
  except OverflowError:return math.copysign(math.inf,x)
 x&=(1<<(64 if t=='u64' else 32))-1
 return x-(1<<32) if t=='i32' and x>=1<<31 else x

def frames(t,merged):
 rng=random.Random(2901);n=lambda x:rounded(x,t)
 if t=='f32':
  special=[0.0,-0.0,{'F32Bits':0x7fc00123},{'F32Bits':0x7f800000},{'F32Bits':0xff800000}]
  rows=[[[],3.0,7.0],[[0.,-0.,1.,3.,7.,8.],3.,7.],[special,3.,-3.],[special,{'F32Bits':0x7fc00000},3.],[special,3.,{'F32Bits':0x7fc00123}],[[rng.randrange(-100,100)/8 for _ in range(17)],3.,7.]]
 else:
  bits=64 if t=='u64' else 32;high=(1<<31)-1 if t=='i32' else (1<<bits)-1;low=-(1<<31) if t=='i32' else 0
  rows=[[[],7,n(-3)],[[0,1,7,8,63,127,high,low],63,7],[[high,low,high,1,0],7,n(-3)],[[1,2,3,4,5],3,0],[[n(rng.getrandbits(bits)) for _ in range(17)],n(rng.getrandbits(bits)),n(rng.getrandbits(bits))]]
 return [[xs,list(reversed(xs[::2])),seed,k] if merged else [xs,seed,k] for xs,seed,k in rows]

def oracle(name,args):
 t=name.rsplit('_',1)[1];held='heldout' in name;merged='_merged_' in name
 xs,ys,seed,k=args if merged else (args[0],[],args[1],args[2]);xs=[number(x) for x in xs];ys=[number(x) for x in ys];seed,k=number(seed),number(k);n=lambda x:rounded(x,t)
 if not merged:
  p=(lambda x:(x<k if x>seed else x==k)) if held else (lambda x:(x<k if x<seed else x>k))
  return sum(bool(p(x)) for x in xs)
 f=(lambda x:n(seed-x) if x>k else n(x+seed)) if held else (lambda x:n(n(x*k)+seed) if x<seed else n(x-k))
 return [f(x) for x in xs+ys]

class Pipeline29(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  BASE.mkdir(parents=True,exist_ok=True);cls.commands=[];cls.outputs=[]
  cls.path=BASE/'checks';cls.path.mkdir(exist_ok=True)
  assert hashlib.sha256(COMPILER.read_bytes()).hexdigest()=='c0f3651f11c04b2a4f30740a1239f3192af52c3cdff4523076456624cc557bbc'
  cls.old=Store(ROOT/'knowledge',ROOT/'knowledge/store/snapshots'/f'{PIN}.json')
  cls.originals=[];static=[]
  for name,t,source in source_functions()+source_functions(True):
   folder=cls.path/name;folder.mkdir(exist_ok=True);src=folder/'source.ink';core=folder/'input.core.json';sem=folder/'subject.json'
   src.write_text('module Pipeline29;\n'+source+'\n');cls.run_(COMPILER,'emit-core',src,'-o',core);cls.run_(COMPILER,'emit-semantic',core,'--core','-o',sem)
   cp=json.loads(core.read_text());subject=json.loads(sem.read_text());rows=specialize(subject,cp)
   assert len(rows)==1,(name,rows)
   static+=rows;cls.originals.append(dict(name=name,type=t,source=src,core=core,subject=subject,row=rows[0],folder=folder))
  cls.store=publish(BASE/'validated-store',static)
  (BASE/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v,id=identity(semantic_entry(v)),role='definition_bound_source_certificate',dependencies=v['dependencies']) for n,v in static],indent=2)+'\n')
  cls.run_(COMPILER,'knowledge-check',BASE/'dummy.core.json',cls.store.root/'view.json')
 @classmethod
 def run_(cls,*args):
  p=subprocess.run(list(map(str,args)),capture_output=True,text=True);cls.commands.append(dict(argv=list(map(str,args)),exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr));(BASE/'test-commands.json').write_text(json.dumps(cls.commands,indent=2)+'\n')
  if p.returncode:raise AssertionError(p.stderr)
  try:return json.loads(p.stdout)
  except json.JSONDecodeError:return p.stdout
 def test_novelty_and_role_counts(self):
  self.assertEqual(len(self.old.members()),1831);support,roots=grouped_laws();self.assertEqual((len(support),len(roots)),(7,7))
  fresh={identity(semantic_entry(v)) for _,v in named_laws()};self.assertFalse(fresh&set(self.old.members()))
  endpoints={alpha(v) for _,v in roots}
  for oid in self.old.members():
   p=self.old.object(oid)['payload']
   if isinstance(p.get('from'),dict) and 'node' in p['from']:self.assertNotIn(alpha(p),endpoints)
  self.assertTrue(all(identity(semantic_entry(v)) in self.old.members() for _,v in reference_laws()))
  (BASE/'novelty.json').write_text(json.dumps(dict(prior=PIN,prior_entries=1831,new_identities=2,optimization_endpoints=7,proof_supports=7,old_reference_laws=4,roles=law_roles()),indent=2)+'\n')
 def test_all_typed_replays_independent_arrays_and_context_mismatch(self):
  records=[]
  for unit in self.originals:
   name,t,core,folder=unit['name'],unit['type'],unit['core'],unit['folder'];_,l=unit['row'];oid=identity(semantic_entry(l));subject=unit['subject'];body=subject['functions'][name]
   app=dict(function=name,path=[],law=oid,arguments={k:var(v,k) for k,v in l['params'].items()},premises=[])
   package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=self.store.bundle([oid]),applications=[app]);sel=folder/'selection.json';sel.write_bytes(canonical(package)+b'\n');receipt=self.run_(COMPILER,'check-selection',core,sel)
   selected=folder/'selected.core.json';self.run_(COMPILER,'emit-core',core,'--core','--selection',sel,'-o',selected)
   sem=folder/'selected.subject.json';self.run_(COMPILER,'emit-semantic',selected,'--core','-o',sem);term=json.loads(sem.read_text())['functions'][name]
   if '_merged_' not in name:self.assertNotIn('method:scan',json.dumps(term));self.assertNotIn('method:map_indexed',json.dumps(term))
   for i,args in enumerate(frames(t,'_merged_' in name)):
    p=folder/f'args-{i}.json';p.write_text(json.dumps(args)+'\n')
    before=self.run_(COMPILER,'run',core,name,p,'--core');after=self.run_(COMPILER,'run',selected,name,p,'--core');self.assertEqual(before,after)
    bits=lambda x:x['F32Bits'] if isinstance(x,dict) else struct.unpack('<I',struct.pack('<f',x))[0]
    if t=='f32' and isinstance(before,list):self.assertEqual(list(map(bits,before)),list(map(bits,after)))
    expected=oracle(name,args)
    if isinstance(expected,list):
     self.assertEqual(len(before),len(expected))
     for actual,e in zip(before,expected):
      if t=='f32' and (isinstance(actual,dict) or not math.isfinite(e)):continue
      self.assertEqual(bits(actual),bits(e)) if t=='f32' else self.assertEqual(actual,e)
    else:self.assertEqual(before,expected)
    records.append(dict(name=name,frame=i,passed=True,complete_original_selected_equal=True,independent_oracle='count/finite array elements; exceptional F32 exact original-selected bits'))
   records_path=folder/'replay.json';records_path.write_text(json.dumps(receipt,indent=2)+'\n')
  (BASE/'interpreter.json').write_text(json.dumps(dict(status='passed',source_instances=len(self.originals),frames=len(records),records=records),indent=2)+'\n')
  # Rehash the input package correctly after modifying a transitive predicate;
  # stale helper definitions must still prevent contextual certificate replay.
  unit=next(x for x in self.originals if x['name']=='pipeline_scan_telemetry_u32');cp=json.loads(unit['core'].read_text());f=next(f for f in cp['program']['functions'] if f['name']=='passes');f['body']={'Bool':False}
  changed=unit['folder']/'changed.core.json';changed.write_bytes(canonical(cp)+b'\n');s=unit['folder']/'changed.subject.json';self.run_(COMPILER,'emit-semantic',changed,'--core','-o',s)
  package=json.loads((unit['folder']/'selection.json').read_text());package['input_core_sha256']=json.loads(s.read_text())['input_core_sha256'];bad=unit['folder']/'changed.selection.json';bad.write_bytes(canonical(package)+b'\n');p=subprocess.run([str(COMPILER),'check-selection',str(changed),str(bad)],capture_output=True,text=True)
  self.assertNotEqual(p.returncode,0);(BASE/'context-mismatch.json').write_text(json.dumps(dict(status='rejected',exit_code=p.returncode,stderr=p.stderr,correctly_rehashed_input=True),indent=2)+'\n')
 def test_generalized_nonzero_initial_state_and_wrapping_nat_offsets(self):
  probes=[]
  for name,root in grouped_laws()[1]:
   family=name.split('_')[0];t=name.rsplit('_',1)[1].upper();s=value(t);ls=value({'List':t});xs=var(ls,'xs')
   starts=[word(t,1),word(t,(1<<(64 if t=='U64' else 32))-1)] if family=='scan' else [nat(2**32-1),nat(2**32+7)]
   zero=word(t,0) if family=='scan' else nat(0)
   for start in starts:
    def replace(v):
     if v==zero:return start
     if isinstance(v,dict):return {k:replace(x) for k,x in v.items()}
     if isinstance(v,list):return [replace(x) for x in v]
     return v
    l=copy.deepcopy(root);l['proof']=replace(l['proof']);stage=op(ls,'scan.acc',xs,start) if family=='scan' else op(ls,'indexed.from',xs,start,var(root['params']['f'],'f'))
    l['from']=op(value('U64'),'call:count',stage);probes.append((name+'_'+str(start['node']),l))
  st=publish(self.path/'initial-state-probes',probes);self.run_(COMPILER,'knowledge-check',BASE/'dummy.core.json',st.root/'view.json')
  (BASE/'initial-state-probes.json').write_text(json.dumps(dict(status='checked',probes=len(probes),indexed_starts=[2**32-1,2**32+7],scope='Semantic initial-state/Nat-offset probes; no physical array of length2^32 executed.'),indent=2)+'\n')
 def test_correctly_hashed_false_equations_reject(self):
  root=dict(grouped_laws()[1])['scan_cardinality_erasure_u32'];bad=copy.deepcopy(root);bad['to']=binary('+',bad['to'],word('U64',1))
  wrong=copy.deepcopy(root);ls=value({'List':'U32'});wrong['params']['ys']=ls;wrong['to']['node']['Op'][1][0]=var(ls,'ys')
  deps={identity(semantic_entry(v)):semantic_entry(v) for _,v in named_laws()};receipts=[]
  for name,v in [('off_by_one',bad),('wrong_receiver',wrong)]:
   objects=dict(deps);obj=semantic_entry(v);oid=identity(obj);objects[oid]=obj;st=Store.publish(self.path/'false'/name,objects.values());view=st.root/'view.json';view.write_bytes(canonical(st.bundle([oid]))+b'\n');p=subprocess.run([str(COMPILER),'knowledge-check',str(BASE/'dummy.core.json'),str(view)],capture_output=True,text=True)
   self.assertNotEqual(p.returncode,0);receipts.append(dict(name=name,id=oid,exit_code=p.returncode,stderr=p.stderr,content_hash_valid=True))
  (BASE/'false-controls.json').write_text(json.dumps(dict(status='rejected',receipts=receipts),indent=2)+'\n')
if __name__=='__main__':unittest.main()
