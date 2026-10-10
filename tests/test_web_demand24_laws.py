"""Unconditional transformed-fallback heads and composed first-match demand."""
import copy,hashlib,json,math,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import arrow,bound,lam,law,op,term,value,var,word
from producers.web_demand24_laws import named_laws,grouped_laws,source_functions,specialize,publish,law_roles,PIN
ROOT=Path(__file__).resolve().parents[1];COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs';COST=ROOT.parent/'reports/web-stack-proofs-23-2026-10-11/cpu-cost-model.json'

def alpha(v):
    seen={}
    def visit(x):
        if isinstance(x,dict):
            if set(x)=={'Free'}:
                n=x['Free'];seen.setdefault(n,'v'+str(len(seen)));return {'Free':seen[n]}
            return {k:visit(x[k]) for k in sorted(x)}
        if isinstance(x,list):return [visit(y) for y in x]
        return x
    return canonical(visit([v['from'],v['to']]))

def number(x):return struct.unpack('<f',struct.pack('<I',x['F32Bits']))[0] if isinstance(x,dict) else x

def norm(x,t):
    if t=='f32':
        try:return struct.unpack('<f',struct.pack('<f',x))[0]
        except OverflowError:return math.copysign(math.inf,x)
    x&=(1<<(64 if t=='u64' else 32))-1
    return x-(1<<32) if t=='i32' and x>=1<<31 else x

def oracle(name,args,staged):
    t=name.rsplit('_',1)[1];n=lambda x:norm(x,t);xs,seed,k=args;xs=[n(number(x)) for x in xs];seed,k=n(number(seed)),n(number(k));held='heldout' in name;filtered='filtered' in name
    f=lambda x:(n(n(x*x)+seed) if x<k else n(n(x-seed)*n(x+k))) if held else (n(n(x*k)+seed) if x>k else n(seed-x))
    p=lambda x:x<k if held else x>seed
    if staged:
        accepted=[x for x in xs if p(x)] if filtered else xs[:];mapped=[f(x) for x in accepted];fallback=f(seed)
        return mapped[0] if mapped else fallback
    selected=next((x for x in xs if p(x)),seed) if filtered else (xs[0] if xs else seed)
    return f(selected)

def frames(t):
    r=random.Random(2401)
    if t=='f32':
        nan={'F32Bits':0x7fc00123};inf={'F32Bits':0x7f800000};neg={'F32Bits':0xff800000}
        return [[[],2.0,3.0],[[0.0,-0.0,1.0,2.0,3.0,8.0],2.0,3.0],[[nan,inf,neg,0.0,-0.0],2.0,-3.0],[[0.0,-0.0,1.0,-1.0],nan,2.0],[[0.0,-0.0,1.0,-1.0],2.0,nan],[[0.0,-0.0,1.0,-1.0],-0.0,inf],[[1e20,-1e20,1.5,-2.0],-2.0,1e20],[[0.0,-0.0,1.0,-1.0],neg,-2.0],[[r.randrange(-1000,1000)/8 for _ in range(19)],17.25,-3.0]]
    bits=64 if t=='u64' else 32;n=lambda x:norm(x,t);hi=(1<<31)-1 if t=='i32' else (1<<bits)-1;lo=-(1<<31) if t=='i32' else 0
    return [[[],7,n(-3)],[[0,1,7,8,hi,lo],7,n(-3)],[[hi,lo,hi,1,0],7,n(-3)],[[1,2,3,4,5],3,hi],[[n(r.getrandbits(bits)) for _ in range(19)],n(r.getrandbits(bits)),n(r.getrandbits(bits))]]

class Demand24Tests(unittest.TestCase):
    def setUp(self):
        self.commands=[];archive=os.environ.get('INK_DEMAND24_EVIDENCE')
        if archive:self.directory=Path(archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True);self.archive=True
        else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-demand24-');self.directory=Path(self.tmp.name);self.archive=False
    def tearDown(self):
        if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
        else:self.tmp.cleanup()
    def command(self,*args,success=True):
        r=subprocess.run(list(map(str,args)),text=True,capture_output=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
        if success:self.assertEqual(r.returncode,0,r.stderr)
        return r
    def compile(self,name,text):
        src=self.directory/(name+'.ink');src.write_text('module Demand24;\n'+text+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');self.command(COMPILER,'emit-core',src,'-o',core);self.command(COMPILER,'emit-semantic',core,'--core','-o',sem);return src,core,json.loads(sem.read_text())
    def test_fresh_endpoints_and_full_prior_source_opportunities(self):
        from producers.beta_sharing17 import derive
        old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1688);self.assertEqual(len(named_laws()),8);roots,deploy=grouped_laws();self.assertEqual((len(roots),len(deploy)),(4,4));self.assertEqual(list(law_roles().values()).count('deployment_composition'),4)
        endpoints={alpha(v) for _,v in named_laws()};generic=[];self.assertFalse({identity(semantic_entry(v)) for _,v in named_laws()}&set(old.members()))
        for i in sorted(old.members()):
            o=old.object(i);v=dict(o['payload'],schema=1,semantics=o['semantics'],dependencies=o['dependencies'])
            if all(k in v for k in ('params','from','to','proof')) and isinstance(v['from'],dict) and 'node' in v['from']:
                self.assertNotIn(alpha(v),endpoints);generic.append(('prior_'+i,v))
        records=[];accepted=[]
        for name,t,text in source_functions()+source_functions(True):
            if t!='u32':continue
            src,core,subject=self.compile(name,text);proposals=derive(subject,generic);checks=[]
            for j,(label,v) in enumerate(proposals):
                objects=list(old.bundle(v['dependencies'])['objects'].values())+[semantic_entry(v)];st=Store.publish(self.directory/(name+'-old-'+str(j)),objects,{label:identity(semantic_entry(v))});view=st.root/'view.json';view.write_bytes(canonical(st.bundle([identity(semantic_entry(v))]))+b'\n');r=self.command(COMPILER,'knowledge-check',core,view,success=False);checks.append(dict(name=label,id=identity(semantic_entry(v)),exit_code=r.returncode,stderr=r.stderr,target=v['to']))
                if r.returncode==0:accepted.append((label,v))
            valid=[r for r in checks if r['exit_code']==0]
            if 'filtered' in name:
                self.assertTrue(any('method:map' not in json.dumps(r['target']) and 'call:foldr' in json.dumps(r['target']) for r in valid),'prior23 first-match fold frontier must be offered fairly')
            else:
                self.assertTrue(all('method:map' in json.dumps(r['target']) for r in valid),'old arithmetic normalization may change fallback but retains mapped materialization')
            records.append(dict(function=name,proposals=checks,accepted_first_steps=len(valid),retained_map_first_steps=sum('method:map' in json.dumps(r['target']) for r in valid),old_first_match_fold_steps=sum('call:foldr' in json.dumps(r['target']) and 'method:map' not in json.dumps(r['target']) for r in valid)))
        (self.directory/'old-opportunities.json').write_text(json.dumps(dict(prior_snapshot=PIN,prior_entries=1688,old_semantic_laws=len(generic),sources=records,accepted_source_witnesses=[dict(name=n,law=v) for n,v in accepted],scope='Every prior semantic law offered; admitted old first-match fold targets are fair old opportunities, not fresh generic innovations. Parent explores bounded old closure symmetrically.'),indent=2)+'\n')
    def test_all_typed_default_applications_replay_and_interpreter(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08');rows=source_functions()+source_functions(True);src,core,subject=self.compile('all','\n'.join(s for _,_,s in rows));derived=specialize(subject);self.assertEqual(len(derived),24);st=publish(self.directory/'isolated',derived);admit=self.command(COMPILER,'knowledge-check',core,st.root/'view.json');apps=[];searches=[]
        for name,t,text in rows:
            unit,uc,_=self.compile(name,text);selection=unit.with_suffix('.selection.json');r=self.command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',512,'--compact-output','-o',selection);searches.append(json.loads(r.stdout));s=json.loads(selection.read_text());self.assertEqual(len(s['applications']),1,(name,s['applications']));apps+=s['applications']
        sel=self.directory/'all.selection.json';sel.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');replay=self.command(COMPILER,'check-selection',core,sel);selected=self.directory/'selected.core.json';self.command(COMPILER,'emit-core',src,'--selection',sel,'-o',selected);sem=selected.with_suffix('.semantic.json');self.command(COMPILER,'emit-semantic',selected,'--core','-o',sem);terms=json.loads(sem.read_text())['functions'];records=[]
        for name,t,text in rows:
            encoded=json.dumps(terms[name]);self.assertNotIn('method:map',encoded);self.assertNotIn('method:filter',encoded);self.assertEqual(encoded.count('call:foldr'),int('filtered' in name))
            for i,args in enumerate(frames(t)):
                path=self.directory/f'args-{t}-{i}.json';path.write_text(json.dumps(args)+'\n');before=json.loads(self.command(COMPILER,'run',src,name,path).stdout);after=json.loads(self.command(COMPILER,'run',selected,name,path,'--core').stdout);self.assertEqual(before,after);a,b=oracle(name,args,True),oracle(name,args,False)
                if t=='f32':
                    actual=number(before)
                    if math.isnan(a):self.assertTrue(math.isnan(b) and math.isnan(actual))
                    else:self.assertEqual(struct.pack('<f',a),struct.pack('<f',b));self.assertEqual(struct.pack('<f',a),struct.pack('<f',actual))
                else:self.assertEqual(a,b);self.assertEqual(a,before)
                records.append(dict(function=name,type=t,arguments=args,original=before,selected=after))
        (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v) for n,v in derived],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(generic_roots=4,deployment_compositions=4,typed_source_certificates=len(derived),default_selected_functions=16,typed_frames=len(records),interpreter_runs=2*len(records),admission=json.loads(admit.stdout),replay=json.loads(replay.stdout),searches=searches,gpu_builds=0,timing_calls=0),indent=2)+'\n')
    def test_fallback_capture_false_controls_and_index_limit(self):
        src,core,_=self.compile('controls',source_functions()[0][2]);s,ls=value('U32'),value({'List':'U32'});f=lam(s,op(s,'binary:+',bound(s,0),word('U32',1)));nil=term(ls,'Nil');mapped=op(ls,'method:map',nil,f)
        source=op(s,'method:at_or',mapped,word('U32',0),word('U32',3));target=op(s,'apply',f,op(s,'method:at_or',nil,word('U32',0),word('U32',3)));false_fallback=law({},source,target)
        false_filter=copy.deepcopy(grouped_laws()[1][0][1]);false_filter['to']=op(s,'apply',var(arrow(s,s),'f'),op(s,'method:at_or',var(ls,'xs'),word('U32',0),var(s,'z')));false_filter['proof']='Normalize';failures=[]
        for label,v in [('untransformed-empty-fallback',false_fallback),('dropped-selection-predicate',false_filter)]:
            st=publish(self.directory/label,[(label,v)]);r=self.command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(label=label,id=identity(semantic_entry(v)),stderr=r.stderr))
        self.assertEqual(specialize(dict(functions={'mismatch':source})),[])
        # Unknown first-class callback does not get guessed from fallback syntax.
        live=var(arrow(s,s),'unknown');bad=op(s,'method:at_or',op(ls,'method:map',var(ls,'xs'),live),word('U32',0),var(s,'z'));self.assertEqual(specialize(dict(functions={'unknown':bad})),[])
        nested=lam(s,op(s,'apply',lam(s,op(s,'binary:+',bound(s,0),var(s,'captured'))),bound(s,0)));z=var(s,'unrelated_default');original=op(s,'method:at_or',op(ls,'method:map',var(ls,'xs'),nested),word('U32',0),op(s,'apply',nested,z));rows=specialize(dict(functions={'unrelated_export':original}));self.assertTrue(rows);st=publish(self.directory/'captured',rows);self.command(COMPILER,'knowledge-check',core,st.root/'view.json')
        # Dynamic-index identity is sound, but the frozen normalizer unfolds
        # at_or only for concrete Word indices. Preserve unsupported attempt.
        dynamic=copy.deepcopy(grouped_laws()[0][0][1]);dynamic['params']['index']=s;dynamic['from']['node']['Op'][1][1]=var(s,'index');dynamic['to']['node']['Op'][1][1]['node']['Op'][1][1]=var(s,'index');st=publish(self.directory/'dynamic-index-unproved',[('dynamic-index',dynamic)]);r=self.command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr)
        (self.directory/'controls.json').write_text(json.dumps(dict(false_controls=failures,counterexamples=dict(empty_fallback=dict(xs=[],z=3,mapper='x+1',source=3,false_target=4),dropped_filter=dict(xs=[1,7],z=2,predicate='x>3',mapper='x+1',source=8,false_target=2)),nested_capture_checked=True,wrong_fallback_unmatched=True,unknown_callback_not_guessed=True,dynamic_index=dict(status='unsupported proof attempt, not a false mathematical statement',stderr=r.stderr)),indent=2)+'\n')

if __name__=='__main__':unittest.main()
