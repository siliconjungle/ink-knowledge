"""Generalized index induction, checked source applications and independent arrays."""
import copy,hashlib,json,math,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import bound,lam,law,nat,op,term,value,var,word
from producers.web_indexed22_laws import named_laws,grouped_laws,optimization_laws,publish,source_functions,specialize
ROOT=Path(__file__).resolve().parents[1];COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs'
PIN='edd38a3302391d76195c377189a95c4f9f893c497198b2c599ce6002df906d37'
COST=ROOT.parent/'reports/web-stack-proofs-20-2026-10-11/cpu-cost-model.json'

def alpha_endpoints(v):
    names={}
    def visit(x):
        if isinstance(x,dict):
            if set(x)=={'Free'}:
                n=x['Free'];names.setdefault(n,'v'+str(len(names)));return {'Free':names[n]}
            return {k:visit(x[k]) for k in sorted(x)}
        if isinstance(x,list):return [visit(y) for y in x]
        return x
    return canonical(visit([v['from'],v['to']]))

def number(v):return struct.unpack('<f',struct.pack('<I',v['F32Bits']))[0] if isinstance(v,dict) else v

def norm(v,t):
    if t=='f32':
        try:return struct.unpack('<f',struct.pack('<f',v))[0]
        except OverflowError:return math.copysign(math.inf,v)
    v&=(1<<(64 if t=='u64' else 32))-1
    return v-(1<<32) if t=='i32' and v>=1<<31 else v

def oracle(name,args,staged):
    t=name.rsplit('_',1)[1];xs,seed,k=args;n=lambda v:norm(v,t)
    ingress=lambda v:n(number(v)) if t=='f32' else number(v)
    xs=list(map(ingress,xs));seed,k=ingress(seed),ingress(k);held='heldout' in name
    if held:
        f=lambda i,x:(x if x>k else seed) if (i&0xffffffff)%3==0 else n(x+k)
        g=lambda i,x:n(seed-x) if (i&0xffffffff)%2==0 else n(x*3)
        h=lambda a,b:n(n(a*b)+seed) if a>b else n(a+n(b*k))
    else:
        f=lambda i,x:n(x+k) if (i&0xffffffff)%2==0 else n(x-seed)
        g=lambda i,x:n(n(x*3)+k) if (i&0xffffffff)%3==0 else n(x+seed)
        h=lambda a,b:n(a+n(b*k)) if a<b else n(a-n(b*k))
    left=lambda i,x:x if name.startswith('indexed_right_zip') else f(i,x)
    right=lambda i,x:x if name.startswith('indexed_left_zip') else g(i,x)
    if staged:
        a=[left(i,x) for i,x in enumerate(xs)];b=[right(i,x) for i,x in enumerate(xs)]
        return [h(x,y) for x,y in zip(a,b)]
    return [h(left(i,x),right(i,x)) for i,x in enumerate(xs)]

def frames(t):
    rng=random.Random(2103)
    if t=='f32':
        special=[{'F32Bits':0x7fc00123},{'F32Bits':0x7f800000},{'F32Bits':0xff800000},0.0,-0.0]
        rows=[[[],2.0,3.0],[[0.0,-0.0,1.0,2.0,3.0,8.0],2.0,3.0],[special,2.0,-3.0],
              [[0.0,-0.0,1.0,-1.0],{'F32Bits':0x7fc00000},2.0],[[0.0,-0.0,1.0,-1.0],2.0,{'F32Bits':0x7fc00000}],
              [[0.0,-0.0,1.0,-1.0],-0.0,{'F32Bits':0x7f800000}],[[1e20,-1e20,1.5,-2.0],-2.0,1e20],
              [[0.0,-0.0,1.0,-1.0],{'F32Bits':0xff800000},-2.0]]
        rows.append([[rng.randrange(-1000,1000)/8 for _ in range(17)],17.25,-3.0]);return rows
    bits=64 if t=='u64' else 32;hi=(1<<31)-1 if t=='i32' else (1<<bits)-1;lo=-(1<<31) if t=='i32' else 0
    return [[[],7,norm(-3,t)],[[0,1,7,8,63,127,hi,lo],63,7],[[hi,lo,hi,1,0],7,norm(-3,t)],[[1,2,3,4,5],3,hi],
            [[norm(rng.getrandbits(bits),t) for _ in range(17)],norm(rng.getrandbits(bits),t),norm(rng.getrandbits(bits),t)]]

class Indexed22Tests(unittest.TestCase):
    def setUp(self):
        self.commands=[];archive=os.environ.get('INK_INDEXED22_EVIDENCE')
        if archive:self.directory=Path(archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True);self.archive=True
        else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-indexed22-');self.directory=Path(self.tmp.name);self.archive=False
    def tearDown(self):
        if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
        else:self.tmp.cleanup()
    def run_command(self,*args,success=True):
        r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
        if success:self.assertEqual(r.returncode,0,r.stderr)
        return r
    def test_twelve_fresh_public_endpoints_and_twelve_generalized_supports(self):
        old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1588)
        supports,roots=grouped_laws();self.assertEqual(len(supports),12);self.assertEqual(len(roots),12)
        ids={identity(semantic_entry(v)) for _,v in named_laws()};self.assertEqual(len(ids),24);self.assertFalse(ids&set(old.members()))
        endpoints={alpha_endpoints(v) for _,v in roots}
        for oid in old.members():
            p=old.object(oid)['payload']
            if isinstance(p.get('from'),dict) and 'node' in p['from']:self.assertNotIn(alpha_endpoints(p),endpoints)
        support_ids={identity(semantic_entry(v)) for _,v in supports}
        self.assertTrue(all(set(v['dependencies'])<=support_ids and len(v['dependencies'])==1 for _,v in roots))
        (self.directory/'novelty.json').write_text(json.dumps(dict(baseline_snapshot=PIN,baseline_entries=1588,public_endpoints=12,beta_supports=12,names={n:identity(semantic_entry(v)) for n,v in named_laws()}),indent=2)+'\n')
    def test_admission_all_typed_source_applications_replay_reify_and_whole_arrays(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        rows=source_functions()+source_functions(True);src=self.directory/'typed.ink';src.write_text('module Indexed22;\n'+'\n'.join(r[2] for r in rows)+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json')
        self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',sem);original=json.loads(sem.read_text());derived=specialize(original);self.assertEqual(len(derived),24);st=publish(self.directory/'isolated',derived);self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json');apps=[];searches=[]
        for name,t,text in rows:
            unit=self.directory/(name+'.ink');unit.write_text('module Unit22;\n'+text+'\n');uc=unit.with_suffix('.core.json');sel=unit.with_suffix('.selection.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc)
            r=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',512,'--compact-output','-o',sel);searches.append(json.loads(r.stdout));selection=json.loads(sel.read_text());self.assertEqual(len(selection['applications']),1,(name,selection['applications']));apps+=selection['applications']
        sel=self.directory/'all.selection.json';sel.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=original['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');replay=self.run_command(COMPILER,'check-selection',core,sel);selected=self.directory/'selected.core.json';self.run_command(COMPILER,'emit-core',src,'--selection',sel,'-o',selected);out=selected.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-semantic',selected,'--core','-o',out);terms=json.loads(out.read_text())['functions'];records=[]
        for name,t,text in rows:
            encoded=json.dumps(terms[name]);self.assertEqual(encoded.count('method:map_indexed'),1);self.assertNotIn('"method:map"',encoded);self.assertNotIn('indexed.from',encoded);self.assertNotIn('method:zip',encoded)
            for i,args in enumerate(frames(t)):
                path=self.directory/f'args-{t}-{i}.json';path.write_text(json.dumps(args)+'\n');eager=oracle(name,args,True);stream=oracle(name,args,False)
                before=json.loads(self.run_command(COMPILER,'run',src,name,path).stdout);after=json.loads(self.run_command(COMPILER,'run',selected,name,path,'--core').stdout);self.assertEqual(before,after);self.assertEqual(len(before),len(args[0]))
                for a,b,actual in zip(eager,stream,before):
                    if t=='f32':
                        actual=number(actual)
                        if math.isnan(a):self.assertTrue(math.isnan(b) and math.isnan(actual))
                        else:self.assertEqual(struct.pack('<f',a),struct.pack('<f',b));self.assertEqual(struct.pack('<f',a),struct.pack('<f',actual))
                    else:self.assertEqual(a,b);self.assertEqual(a,actual)
                records.append(dict(function=name,type=t,arguments=args,original=before,selected=after))
        builds=[]
        for held in (False,True):
            group=[r for r in rows if r[1]=='u32' and ('heldout' in r[0])==held]
            unit=self.directory/f'u32-{int(held)}-gpu.ink';unit.write_text('module Gpu22;\n'+'\n'.join(r[2] for r in group)+'\n');uc=unit.with_suffix('.core.json');us=unit.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc);self.run_command(COMPILER,'emit-semantic',uc,'--core','-o',us);u=json.loads(us.read_text());ua=[a for a in apps if a['function'] in u['functions']];package=unit.with_suffix('.selection.json');package.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=u['input_core_sha256'],knowledge=st.bundle([a['law'] for a in ua]),applications=ua),separators=(',',':'))+'\n');self.run_command(COMPILER,'check-selection',uc,package);sc=unit.with_suffix('.selected.core.json');self.run_command(COMPILER,'emit-core',unit,'--selection',package,'-o',sc);bundle=self.directory/f'u32-{int(held)}-gpu';self.run_command(COMPILER,'build',sc,'--core','--target','webgpu','--zig',ROOT.parent.parent/'toolchain/zig-aarch64-macos-0.15.2/zig','-o',bundle);manifest=json.loads((bundle/'manifest.json').read_text());self.assertEqual(len(manifest['functions']),3)
            for fn in manifest['functions']:self.assertIsNotNone(fn.get('shader'));self.assertIsNone(fn.get('fallback_reason'));self.assertTrue((bundle/fn['shader']).is_file());builds.append(dict(function=fn['name'],shader=fn['shader'],schema=manifest['schema']))
        (self.directory/'gpu-builds.json').write_text(json.dumps(dict(shaders=builds,gpu_calls=0),indent=2)+'\n')
        (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v) for n,v in derived],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(generic_public_roots=12,beta_transport_supports=12,checked_callback_instances=24,typed_frames=len(records),actual_interpreter_runs=2*len(records),replay=json.loads(replay.stdout),searches=searches),indent=2)+'\n')
    def test_prior_compositional_opportunities_on_six_exact_sources(self):
        from producers.beta_sharing17 import derive
        old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');generic=[]
        for oid in sorted(old.members()):
            obj=old.object(oid);p=dict(obj['payload'],schema=1,semantics=obj['semantics'],dependencies=obj['dependencies'])
            if all(k in p for k in ('params','from','to','proof')) and isinstance(p['from'],dict) and 'node' in p['from']:generic.append(('prior_'+oid,p))
        records=[]
        for name,t,text in source_functions()+source_functions(True):
            if t!='u32':continue
            src=self.directory/(name+'.ink');src.write_text('module Prior22;\n'+text+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',sem);subject=json.loads(sem.read_text());rows=derive(subject,generic);self.assertEqual(len(rows),0,(name,[n for n,_ in rows]));records.append(dict(function=name,old_only_source_certificates=len(rows),subject_sha256=hashlib.sha256(sem.read_bytes()).hexdigest()))
        (self.directory/'prior-opportunities.json').write_text(json.dumps(dict(prior=PIN,entries=1588,old_semantic_laws=len(generic),subjects=records,scope='Same strict checked-sharing opportunity; no old first-step certificate exists so two-step expansion has no frontier. Parent independently offers fair catalogue planning.'),indent=2)+'\n')
    def test_index_wrap_checked_normalization_and_hash_valid_false_controls(self):
        src=self.directory/'negative.ink';src.write_text('module Negative22;\n'+source_functions()[0][2]+'\n');core=src.with_suffix('.core.json');self.run_command(COMPILER,'emit-core',src,'-o',core)
        # The internal primitive is not an executable public API. A two-item
        # closed semantic witness tests Nat index 2^32-1 then its wrapped zero.
        s,ls=value('U32'),value({'List':'U32'});data=term(ls,{'Cons':[word('U32',7),term(ls,{'Cons':[word('U32',11),term(ls,'Nil')]})]})
        callback=lam(s,lam(s,bound(s,1)));source=op(ls,'indexed.from',data,nat((1<<32)-1),callback)
        target=term(ls,{'Cons':[word('U32',(1<<32)-1),term(ls,{'Cons':[word('U32',0),term(ls,'Nil')]})]})
        wrap=law({},source,target);st=publish(self.directory/'wrap',[('closed-index-wrap',wrap)]);self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json')
        # The indexed zip itself must use one shared generalized start index.
        checks=[]
        for start_index in (7,(1<<32)-1):
            identity_callback=lam(s,lam(s,bound(s,0)))
            projection=lam(s,lam(s,bound(s,1)))
            lhs=op(ls,'method:zip',op(ls,'indexed.from',data,nat(start_index),callback),op(ls,'indexed.from',data,nat(start_index),identity_callback),projection)
            expected=[start_index&0xffffffff,(start_index+1)&0xffffffff]
            rhs=term(ls,{'Cons':[word('U32',expected[0]),term(ls,{'Cons':[word('U32',expected[1]),term(ls,'Nil')]})]})
            witness=law({},lhs,rhs);st=publish(self.directory/('zip-start-'+str(start_index)),[('closed-zip-start',witness)]);self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json');checks.append(dict(start=start_index,expected=expected,content_id=identity(semantic_entry(witness))))
        (self.directory/'closed-zip-starts.json').write_text(json.dumps(checks,indent=2)+'\n')
        # Hash-valid false endpoints: reset the live index; use a different receiver.
        bad=copy.deepcopy(optimization_laws()[0][1])
        def reset(v):
            if isinstance(v,dict):
                if v.get('node')=={'Bound':1} and v.get('sort')==value('U32'):v['node']={'Word':0}
                else:
                    for x in v.values():reset(x)
            elif isinstance(v,list):
                for x in v:reset(x)
        reset(bad['to']);bad['proof']='Normalize'
        receiver=copy.deepcopy(optimization_laws()[0][1]);receiver['params']['ys']=ls
        receiver['from']['node']['Op'][1][1]['node']['Op'][1][0]=var(ls,'ys');receiver['proof']='Normalize'
        shifted=copy.deepcopy(wrap);shifted['to']['node']['Cons'][1]['node']['Cons'][0]=word('U32',1)
        failures=[]
        for label,v in [('reset-index',bad),('wrong-receiver',receiver),('miss-wrap',shifted)]:
            st=publish(self.directory/label,[(label,v)]);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(label=label,content_id=identity(semantic_entry(v)),stderr=r.stderr))
        (self.directory/'index-wrap-and-false-controls.json').write_text(json.dumps(dict(valid_wrap_id=identity(semantic_entry(wrap)),start_index=(1<<32)-1,expected_indices=[(1<<32)-1,0],scope='Two-element semantic witness; no enormous public array execution',false_controls=failures),indent=2)+'\n')

if __name__=='__main__':unittest.main()
