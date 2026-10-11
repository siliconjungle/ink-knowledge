"""Typed exact stage transport, source replay and semantic negative controls."""
import copy,hashlib,json,math,random,struct,subprocess,sys,unittest
from pathlib import Path
B=Path(__file__).resolve().parents[2];sys.path[:0]=[str(B/'knowledge'),str(B/'planner')]
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import var,value
from producers.web_pipeline31_laws import named_laws,law_roles,source_functions,specialize,publish
PIN='608c4e67bde5ca82537aa1aad2ef64872b0e4287f7c962579f9776516650b93d';C=B.parent/'toolchain/ink-web-engine-28';R=B/'reports/web-stack-proofs-31-2026-10-11/proofs'

def alpha(l):
 names={}
 def go(v):
  if isinstance(v,dict):
   if set(v)=={'Free'}:names.setdefault(v['Free'],str(len(names)));return dict(Free=names[v['Free']])
   return{k:go(v[k])for k in sorted(v)}
  if isinstance(v,list):return[go(x)for x in v]
  return v
 return canonical(go([l['from'],l['to']]))

def number(x):return struct.unpack('<f',struct.pack('<I',x['F32Bits']))[0]if isinstance(x,dict)else x

def rounded(x,t):
 if t=='f32':
  try:return struct.unpack('<f',struct.pack('<f',x))[0]
  except OverflowError:return math.copysign(math.inf,x)
 x&=(1<<(64 if t=='u64'else 32))-1
 return x-2**32 if t=='i32'and x>=2**31 else x

def div(x,y,t,remainder=False):
 if y==0 or(t=='i32'and x==-2**31 and y==-1):return 0
 q=(abs(x)//abs(y))*(-1 if (x<0)!=(y<0)else 1)
 return x-q*y if remainder else q

def oracle(name,args):
 t=name.rsplit('_',1)[1];xs,seed,k=args;xs=list(map(number,xs));seed,k=number(seed),number(k)
 if 'uniform_prefix'in name:
  c=rounded(div(seed,k,t)+1 if 'heldout'in name else seed+k,t)
  return[rounded((i+1)*c,t)for i in range(len(xs))]
 return [rounded(k-x if x<k else x+k,t)for x in xs if x<seed]

def frames(t,merge):
 r=random.Random(3001)
 if t=='f32':
  special=[0.0,-0.0,{'F32Bits':0x7fc00123},{'F32Bits':0xffc00789},{'F32Bits':0x7f800000},{'F32Bits':0xff800000}]
  rows=[([],3.,7.),([0.,-0.,1.,3.,7.,8.],3.,7.),(special,3.,-3.),(special,{'F32Bits':0x7fc00000},3.),(special,3.,{'F32Bits':0x7fc00123}),([r.randrange(-100,100)/8 for _ in range(16)],3.,7.)]
  ys=[7.,-0.,{'F32Bits':0x7fc00234},1.,-2.]
 else:
  bits=64 if t=='u64'else 32;n=lambda x:rounded(x,t);hi=(1<<31)-1 if t=='i32'else(1<<bits)-1;lo=-(1<<31)if t=='i32'else 0
  rows=[([],7,n(-3)),([0,1,7,8,63,127,hi,lo],63,7),([hi,lo,hi,1,0],7,n(-3)),([1,2,3,4,5],3,0),([n(r.getrandbits(bits))for _ in range(16)],n(r.getrandbits(bits)),n(r.getrandbits(bits))),([0,1,7,8,11],0,97),([0,1,7,8,11],hi,97)]
  if t=='i32':rows.append(([-2**31,-1,0,1,2**31-1],127,-1))
  ys=[n(r.getrandbits(bits))for _ in range(5)]
 result=[[xs,ys,seed,k]if merge else[xs,seed,k]for xs,seed,k in rows]
 if merge:result += [[ys,[],rows[0][1],rows[0][2]],[[],[],rows[0][1],rows[0][2]]]
 return result

class Pipeline31(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  R.mkdir(parents=True,exist_ok=True);cls.commands=[];cls.units=[];static=[]
  (R/'dummy.core.json').write_bytes((B/'reports/web-stack-proofs-30-2026-10-11/proofs/dummy.core.json').read_bytes())
  assert hashlib.sha256(C.read_bytes()).hexdigest()=='c0f3651f11c04b2a4f30740a1239f3192af52c3cdff4523076456624cc557bbc'
  for name,t,source in source_functions()+source_functions(True):
   d=R/'checks'/name;d.mkdir(parents=True,exist_ok=True);src=d/'source.ink';src.write_text('module Pipeline31;\n'+source+'\n');core=d/'input.core.json';sem=d/'subject.json';cls.run_(C,'emit-core',src,'-o',core);cls.run_(C,'emit-semantic',core,'--core','-o',sem)
   subject=json.loads(sem.read_text());cp=json.loads(core.read_text());rows=specialize(subject,cp);assert len(rows)==1,(name,len(rows));static+=rows;cls.units.append(dict(name=name,type=t,folder=d,core=core,subject=subject,row=rows[0]))
  cls.store=publish(R/'validated-store',static);cls.run_(C,'knowledge-check',R/'dummy.core.json',cls.store.root/'view.json')
  (R/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v,id=identity(semantic_entry(v)),role='definition_bound_source_certificate')for n,v in static],indent=2)+'\n')
 @classmethod
 def run_(cls,*args):
  p=subprocess.run(list(map(str,args)),capture_output=True,text=True);cls.commands.append(dict(argv=list(map(str,args)),exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr));(R/'test-commands.json').write_text(json.dumps(cls.commands,indent=2)+'\n');assert not p.returncode,p.stderr
  try:return json.loads(p.stdout)
  except json.JSONDecodeError:return p.stdout
 def test_all_typed_replay_complete_outputs_and_independent_oracle(self):
  records=[]
  for u in self.units:
   name,t,d,core=u['name'],u['type'],u['folder'],u['core'];_,l=u['row'];oid=identity(semantic_entry(l));app=dict(function=name,path=[],law=oid,arguments={k:var(v,k)for k,v in l['params'].items()},premises=[]);package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=u['subject']['input_core_sha256'],knowledge=self.store.bundle([oid]),applications=[app]);sel=d/'selection.json';sel.write_bytes(canonical(package)+b'\n');receipt=self.run_(C,'check-selection',core,sel);(d/'replay.json').write_text(json.dumps(receipt,indent=2)+'\n');selected=d/'selected.core.json';self.run_(C,'emit-core',core,'--core','--selection',sel,'-o',selected)
   self.assertNotIn('call:discarded_value',canonical(l['to']).decode());self.assertIn('method:map_indexed'if 'uniform_prefix'in name else'method:filter',canonical(l['to']).decode());self.assertIn('method:map',canonical(l['to']).decode());self.assertNotIn('method:zip',canonical(l['to']).decode())
   for i,args in enumerate(frames(t,False)):
    argfile=d/f'args-{i}.json';argfile.write_text(json.dumps(args)+'\n');before=self.run_(C,'run',core,name,argfile,'--core');after=self.run_(C,'run',selected,name,argfile,'--core');self.assertEqual(before,after)
    def bits(x):return x['F32Bits']if isinstance(x,dict)else struct.unpack('<I',struct.pack('<f',x))[0]
    expected=oracle(name,args);self.assertEqual(len(before),len(expected))
    for a,e in zip(before,expected):
     if t=='f32':
      if math.isnan(e):continue
      self.assertEqual(bits(a),bits(e))
     else:self.assertEqual(a,e)
    records.append(dict(name=name,frame=i,output_elements=len(before),original_selected_equal=True,finite_oracle_equal=True))
  (R/'interpreter.json').write_text(json.dumps(dict(status='passed',typed_sources=len(self.units),frames=len(records),records=records,scope='Full arrays; wrapping integer and non-NaN F32 independent oracle, exceptional F32 bits compared original/selected. No positions assumed aligned.'),indent=2)+'\n')
 def test_forward_reverse_full_prior_alpha_novelty(self):
  old=Store(B/'knowledge',B/'knowledge/store/snapshots'/f'{PIN}.json');old.members();self.assertEqual(len(old.members()),1891);new={alpha(v):n for n,v in named_laws()};duplicates=[];semantic=0
  for oid in old.members():
   p=old.object(oid)['payload']
   if not isinstance(p.get('from'),dict)or'node'not in p['from']:continue
   semantic+=1
   for direction,q in [('forward',p),('reverse',dict(p,**{'from':p['to'],'to':p['from']}))]:
    if alpha(q)in new:duplicates.append(dict(candidate=new[alpha(q)],prior_id=oid,direction=direction))
  self.assertFalse(duplicates);self.assertFalse({identity(semantic_entry(v))for _,v in named_laws()}&set(old.members()))
  (R/'novelty.json').write_text(json.dumps(dict(status='passed',prior_snapshot=PIN,prior_entries=1891,prior_semantic_pairs=semantic,mathematical_mechanisms=2,orientation_endpoints=8,constant_stream_endpoints=1,proof_supports=18,duplicates=duplicates,roles=law_roles()),indent=2)+'\n')
 def test_constant_scan_nonzero_and_wrapping_nat_offset(self):
  from producers.web_pipeline31_laws import constant_scan_laws
  from producers.semantic_laws import term,law,word
  from producers.beta_specialization15 import instantiate_bound
  from ink_planner.semantic_search import substitute
  support=constant_scan_laws()[1][1];ls=value({'List':'U32'});literal=term(ls,'Nil')
  for x in reversed([0,2**32-1,7]):literal=term(ls,{'Cons':[word('U32',x),literal]})
  checks=[]
  for start in [0,17,2**32-1,2**32,2**32+7]:
   for c in [0,7,2**32-1]:
    args=dict(xs=literal,c=word('U32',c));fn=substitute(support['from'],args);source=instantiate_bound(fn['node']['Lambda'],term('Nat',{'Nat':start}));fn=substitute(support['to'],args);target=instantiate_bound(fn['node']['Lambda'],term('Nat',{'Nat':start}));expected=term(ls,'Nil')
    for i in reversed(range(3)):expected=term(ls,{'Cons':[word('U32',((start+i+1)*c)&(2**32-1)),expected]})
    for kind,endpoint in [('scan',source),('indexed',target)]:
     obj=semantic_entry(law({},endpoint,expected));oid=identity(obj);d=R/'offset-checks'/f'{start}-{c}-{kind}';st=Store.publish(d,[obj]);v=d/'view.json';v.write_bytes(canonical(st.bundle([oid]))+b'\n');self.run_(C,'knowledge-check',R/'dummy.core.json',v)
    checks.append(dict(start=start,constant=c,finite_elements=3,scan_and_indexed_equal_independent_wrapping_values=True))
  (R/'nat-offset-checks.json').write_text(json.dumps(dict(status='passed',checks=checks,scope='Finite three-element semantic normalization at arbitrary nonzero and wrapping Nat start. Does not allocate or test a 2^32-element public list.'),indent=2)+'\n')

 def test_semantic_false_rehashed_context_and_capture_controls(self):
  from producers.semantic_laws import arrow,lam,bound,op
  roots=dict(named_laws());wrong_receiver=copy.deepcopy(roots['filtered_left_projection_erasure_u32']);ls=value({'List':'U32'});wrong_receiver['params']['ys']=ls;wrong_receiver['from']['node']['Op'][1][0]['node']['Op'][1][0]=var(ls,'ys')
  wrong_mapper=copy.deepcopy(roots['filtered_left_projection_erasure_u32']);s=value('U32');wrong_mapper['to']['node']['Op'][1][1]=var(arrow(s,s),'f')
  wrong_index=copy.deepcopy(roots['constant_scan_indexed_u32']);callback=wrong_index['to']['node']['Op'][1][1]['node']['Lambda']['node']['Lambda'];callback['node']['Op'][1][0]=callback['node']['Op'][1][0]['node']['Op'][1][0]
  receipts=[]
  for name,v in [('wrong_receiver',wrong_receiver),('wrong_mapper',wrong_mapper),('wrong_index',wrong_index)]:
   # Publish minimal dependency closure from admitted isolated store.
   obj=semantic_entry(v);oid=identity(obj);objects={oid:obj}
   def add(i):
    if i not in objects:objects[i]=self.store.object(i)
    for d in objects[i]['dependencies']:
     if d not in objects:add(d)
   for i in obj['dependencies']:add(i)
   st=Store.publish(R/'false'/name,objects.values());view=st.root/'view.json';view.write_bytes(canonical(st.bundle([oid]))+b'\n');p=subprocess.run([str(C),'knowledge-check',str(R/'dummy.core.json'),str(view)],capture_output=True,text=True);self.assertNotEqual(p.returncode,0);receipts.append(dict(name=name,id=oid,content_hash_valid=True,exit_code=p.returncode,stderr=p.stderr))
  u=next(x for x in self.units if x['name']=='pipeline31_left_projection_u32');cp=json.loads(u['core'].read_text());next(f for f in cp['program']['functions']if f['name']=='batch_accepts')['body']={'Bool':False};changed=u['folder']/'changed.core.json';changed.write_bytes(canonical(cp)+b'\n');sem=u['folder']/'changed.subject.json';self.run_(C,'emit-semantic',changed,'--core','-o',sem);sel=json.loads((u['folder']/'selection.json').read_text());sel['input_core_sha256']=json.loads(sem.read_text())['input_core_sha256'];path=u['folder']/'changed.selection.json';path.write_bytes(canonical(sel)+b'\n');p=subprocess.run([str(C),'check-selection',str(changed),str(path)],capture_output=True,text=True);self.assertNotEqual(p.returncode,0)
  original=copy.deepcopy(u['subject']);body=original['functions'][u['name']];callback=body['node']['Op'][1][2];callback['node']['Lambda']['node']['Lambda']=op(s,'binary:+',bound(s,1),bound(s,0));self.assertEqual(specialize(original),[])
  (R/'negative-controls.json').write_text(json.dumps(dict(status='rejected',semantic_false=receipts,unused_binder_capture_rejected=True,correctly_rehashed_context_mismatch=dict(exit_code=p.returncode,stderr=p.stderr)),indent=2)+'\n')
if __name__=='__main__':unittest.main()
