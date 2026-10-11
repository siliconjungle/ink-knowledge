"""Checked independent-prefix combination, exact words, unequal lengths and contexts."""
import copy,hashlib,json,random,subprocess,sys,unittest
from pathlib import Path
B=Path(__file__).resolve().parents[2];sys.path[:0]=[str(B/'knowledge'),str(B/'planner')]
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import value,var,word,term,law
from producers.web_pipeline32_laws import named_laws,law_roles,source_functions,specialize,publish
PIN='2611e6bf33c70f66929b27cd8250f4a8e9ccc28ffada49bbb0b3597c1ffce988';C=B.parent/'toolchain/ink-web-engine-28';R=B/'reports/web-stack-proofs-32-2026-10-11/proofs'

def alpha(l):
 names={}
 def go(v):
  if isinstance(v,dict):
   if set(v)=={'Free'}:names.setdefault(v['Free'],str(len(names)));return dict(Free=names[v['Free']])
   return{k:go(v[k])for k in sorted(v)}
  if isinstance(v,list):return[go(x)for x in v]
  return v
 return canonical(go([l['from'],l['to']]))

def wrap(x,t):
 x&=(1<<(64 if t=='u64'else 32))-1
 return x-2**32 if t=='i32'and x>=2**31 else x

def quotient(x,y,t):
 if y==0 or(t=='i32'and x==-2**31 and y==-1):return 0
 return(abs(x)//abs(y))*(-1 if (x<0)!=(y<0)else 1)

def remainder(x,y,t):
 if y==0 or(t=='i32'and x==-2**31 and y==-1):return 0
 return x-quotient(x,y,t)*y

def eager(name,args):
 t=name.rsplit('_',1)[1];xs,ys,seed,k=args
 if 'heldout'in name:
  xs=[wrap(quotient(x,k,t)+seed,t)for x in xs];ys=[wrap(remainder(y,k,t)+k,t)for y in ys]
 def prefix(a):
  state=0;out=[]
  for x in a:state=wrap(state+x,t);out.append(state)
  return out
 xs,ys=prefix(xs),prefix(ys)
 combined=[wrap(x+y if '_add_'in name else x-y,t)for x,y in zip(xs,ys)]
 return[wrap(x+k if x<seed else x-k,t)for x in combined]

def direct(name,args):
 t=name.rsplit('_',1)[1];xs,ys,seed,k=args;total=0;out=[]
 for x,y in zip(xs,ys):
  if 'heldout'in name:x=wrap(quotient(x,k,t)+seed,t);y=wrap(remainder(y,k,t)+k,t)
  total+=x+y if '_add_'in name else x-y
  combined=wrap(total,t);out.append(wrap(combined+k if combined<seed else combined-k,t))
 return out

def frames(t):
 rand=random.Random(3203);n=lambda x:wrap(x,t);bits=64 if t=='u64'else 32;hi=2**31-1 if t=='i32'else 2**bits-1;lo=-2**31 if t=='i32'else 0
 rows=[([],[],7,n(-3)),([],[hi,1],3,7),([hi,1],[],3,7),([0,1,hi,lo,7],[hi,lo,1],7,n(-3)),([lo,hi,lo,hi],[1,2,3,4,5,6],hi,7),([0,1,7,8],[3,4,5,6],3,0),([lo,hi,1,0],[lo,hi,lo,1],hi,-1 if t=='i32'else hi)]
 for nx,ny in [(1,16),(16,1),(16,16),(7,13)]:rows.append(([n(rand.getrandbits(bits))for _ in range(nx)],[n(rand.getrandbits(bits))for _ in range(ny)],n(rand.getrandbits(bits)),n(rand.getrandbits(bits))))
 return rows

class Pipeline32(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  R.mkdir(parents=True,exist_ok=True);cls.commands=[];cls.units=[];static=[]
  assert hashlib.sha256(C.read_bytes()).hexdigest()=='c0f3651f11c04b2a4f30740a1239f3192af52c3cdff4523076456624cc557bbc'
  (R/'dummy.core.json').write_bytes((B/'reports/web-stack-proofs-31-2026-10-11/proofs/dummy.core.json').read_bytes())
  for held in (False,True):
   for name,t,source in source_functions(held):
    d=R/'checks'/name;d.mkdir(parents=True,exist_ok=True);src=d/'source.ink';src.write_text('module Pipeline32;\n'+source+'\n');core=d/'input.core.json';sem=d/'subject.json';cls.run_(C,'emit-core',src,'-o',core);cls.run_(C,'emit-semantic',core,'--core','-o',sem);subject=json.loads(sem.read_text());rows=specialize(subject,json.loads(core.read_text()));assert len(rows)==1,(name,len(rows));static+=rows;cls.units.append(dict(name=name,type=t,folder=d,core=core,subject=subject,row=rows[0]))
  cls.store=publish(R/'validated-store',static);cls.run_(C,'knowledge-check',R/'dummy.core.json',cls.store.root/'view.json')
  (R/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v,id=identity(semantic_entry(v)),role='definition_bound_source_certificate')for n,v in static],indent=2)+'\n')
 @classmethod
 def run_(cls,*args):
  p=subprocess.run(list(map(str,args)),capture_output=True,text=True);cls.commands.append(dict(argv=list(map(str,args)),exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr));(R/'test-commands.json').write_text(json.dumps(cls.commands,indent=2)+'\n');assert not p.returncode,p.stderr
  try:return json.loads(p.stdout)
  except json.JSONDecodeError:return p.stdout
 def test_all_typed_replay_complete_arrays(self):
  records=[]
  for u in self.units:
   name,t,d,core=u['name'],u['type'],u['folder'],u['core'];_,l=u['row'];oid=identity(semantic_entry(l));pkg=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=u['subject']['input_core_sha256'],knowledge=self.store.bundle([oid]),applications=[dict(function=name,path=[],law=oid,arguments={n:var(s,n)for n,s in l['params'].items()},premises=[])]);sel=d/'selection.json';sel.write_bytes(canonical(pkg)+b'\n');receipt=self.run_(C,'check-selection',core,sel);(d/'replay.json').write_text(json.dumps(receipt,indent=2)+'\n');selected=d/'selected.core.json';self.run_(C,'emit-core',core,'--core','--selection',sel,'-o',selected)
   self.assertEqual(canonical(l['to']).decode().count('method:scan'),1)
   for i,args in enumerate(frames(t)):
    beforeargs=copy.deepcopy(args);f=d/f'args-{i}.json';f.write_text(json.dumps(args)+'\n');before=self.run_(C,'run',core,name,f,'--core');after=self.run_(C,'run',selected,name,f,'--core');self.assertEqual(before,after);self.assertEqual(before,eager(name,args));self.assertEqual(before,direct(name,args));self.assertEqual(args,beforeargs);self.assertEqual(len(before),min(len(args[0]),len(args[1])));records.append(dict(name=name,frame=i,output_elements=len(before),equal=True))
  (R/'interpreter.json').write_text(json.dumps(dict(status='passed',typed_sources=len(self.units),frames=len(records),records=records,scope='Complete arrays, wrapping each primitive, unequal independent lists, signed division overflow/zero and random full words; two independent algorithm orderings agree.'),indent=2)+'\n')
 def test_forward_reverse_full_prior_novelty(self):
  st=Store(B/'knowledge',B/'knowledge/store/snapshots'/f'{PIN}.json');st.members();self.assertEqual(len(st.members()),1952);new={alpha(v):n for n,v in named_laws()};duplicates=[];count=0
  for oid in st.members():
   p=st.object(oid)['payload']
   if not isinstance(p.get('from'),dict)or'node'not in p['from']:continue
   count+=1
   for direction,q in [('forward',p),('reverse',dict(p,**{'from':p['to'],'to':p['from']}))]:
    if alpha(q)in new:duplicates.append(dict(candidate=new[alpha(q)],prior_id=oid,direction=direction))
  self.assertFalse(duplicates);self.assertFalse({identity(semantic_entry(v))for _,v in named_laws()}&set(st.members()));(R/'novelty.json').write_text(json.dumps(dict(status='passed',prior_entries=1952,snapshot=PIN,prior_semantic_pairs=count,duplicates=duplicates,mechanisms=1,typed_endpoints=6,supports=12,roles=law_roles()),indent=2)+'\n')
 def test_general_nonzero_state_closed_normalization(self):
  from producers.beta_specialization15 import instantiate_bound
  from ink_planner.semantic_search import substitute
  checks=[];roots=dict(named_laws())
  for t in ('u32','i32','u64'):
   ls=value({'List':t.upper()});literal=lambda xs:self.list_term(xs,t)
   for operation in ('add','subtract'):
    support=roots['paired_scan_'+operation+'_state_'+t]
    for xs,ys,a,b in frames(t)[:7]:
     args=dict(xs=literal(xs));left=instantiate_bound(substitute(support['from'],args)['node']['Lambda'],literal(ys));left=instantiate_bound(left['node']['Lambda'],word(t.upper(),a&((1<<(64 if t=='u64'else 32))-1)));left=instantiate_bound(left['node']['Lambda'],word(t.upper(),b&((1<<(64 if t=='u64'else 32))-1)));right=instantiate_bound(substitute(support['to'],args)['node']['Lambda'],literal(ys));right=instantiate_bound(right['node']['Lambda'],word(t.upper(),a&((1<<(64 if t=='u64'else 32))-1)));right=instantiate_bound(right['node']['Lambda'],word(t.upper(),b&((1<<(64 if t=='u64'else 32))-1)))
     pa,pb=a,b;out=[]
     for x,y in zip(xs,ys):pa=wrap(pa+x,t);pb=wrap(pb+y,t);out.append(wrap(pa+pb if operation=='add'else pa-pb,t))
     objects=[semantic_entry(law({},endpoint,literal(out)))for endpoint in (left,right)];d=R/'state-checks'/f'{t}-{operation}-{len(checks)}';st=Store.publish(d,objects);view=d/'view.json';view.write_bytes(canonical(st.bundle([identity(o)for o in objects]))+b'\n');self.run_(C,'knowledge-check',R/'dummy.core.json',view);checks.append(dict(type=t,operation=operation,lengths=[len(xs),len(ys)],initial=[a,b]))
  (R/'state-checks.json').write_text(json.dumps(dict(status='passed',checks=checks),indent=2)+'\n')
 @staticmethod
 def list_term(xs,t):
  ls=value({'List':t.upper()});result=term(ls,'Nil')
  for x in reversed(xs):result=term(ls,{'Cons':[word(t.upper(),x&((1<<(64 if t=='u64'else 32))-1)),result]})
  return result
 def test_rehashed_semantic_false_and_context_controls(self):
  roots=dict(named_laws());bad1=copy.deepcopy(roots['paired_scan_subtract_reconstruction_u32']);bad1['to']['node']['Op'][1][0]['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']['node']['Op'][0]='binary:+'
  bad2=copy.deepcopy(roots['paired_scan_add_reconstruction_u32']);bad2['to']['node']['Op'][1][0]['node']['Op'][1][1]=var(value({'List':'U32'}),'xs')
  receipts=[]
  for name,v in [('wrong_operation',bad1),('wrong_receiver',bad2)]:
   obj=semantic_entry(v);oid=identity(obj);objects={oid:obj}
   def add(i):
    if i not in objects:objects[i]=self.store.object(i)
    for d in objects[i]['dependencies']:
     if d not in objects:add(d)
   for i in obj['dependencies']:add(i)
   st=Store.publish(R/'false'/name,objects.values());view=st.root/'view.json';view.write_bytes(canonical(st.bundle([oid]))+b'\n');p=subprocess.run([str(C),'knowledge-check',str(R/'dummy.core.json'),str(view)],capture_output=True,text=True);self.assertNotEqual(p.returncode,0);receipts.append(dict(name=name,id=oid,content_hash_valid=True,exit_code=p.returncode,stderr=p.stderr))
  u=next(x for x in self.units if x['name']=='pipeline32_paired_prefix_add_heldout_u32');cp=json.loads(u['core'].read_text());next(f for f in cp['program']['functions']if f['name']=='left_word')['body']={'Num':1};changed=u['folder']/'changed.core.json';changed.write_bytes(canonical(cp)+b'\n');sem=u['folder']/'changed.subject.json';self.run_(C,'emit-semantic',changed,'--core','-o',sem);sel=json.loads((u['folder']/'selection.json').read_text());sel['input_core_sha256']=json.loads(sem.read_text())['input_core_sha256'];path=u['folder']/'changed.selection.json';path.write_bytes(canonical(sel)+b'\n');p=subprocess.run([str(C),'check-selection',str(changed),str(path)],capture_output=True,text=True);self.assertNotEqual(p.returncode,0)
  (R/'negative-controls.json').write_text(json.dumps(dict(status='rejected',semantic_false=receipts,correctly_rehashed_context_mismatch=dict(exit_code=p.returncode,stderr=p.stderr)),indent=2)+'\n')
if __name__=='__main__':unittest.main()
