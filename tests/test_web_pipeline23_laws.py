"""Checked dead prefix-state consumers and independent complete-array oracles."""
import copy,hashlib,json,os,random,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import bound,lam,law,op,term,value,var,word
from producers.web_pipeline23_laws import named_laws,optimization_laws,grouped_laws,source_functions,specialize,publish,law_roles
from tests.test_web_indexed22_laws import alpha_endpoints
ROOT=Path(__file__).resolve().parents[1];COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs'
PIN='95c096ab4a28114fb70c334b662057bd8abfffe135a3198032f4ea38a679bd57'
COST=ROOT.parent/'reports/web-stack-proofs-22-2026-10-11/cpu-cost-model.json'

def normalize(x,t):
    x&=(1<<(64 if t=='u64' else 32))-1
    return x-(1<<32) if t=='i32' and x>=(1<<31) else x

def oracle(name,args,staged):
    t=name.rsplit('_',1)[1];n=lambda x:normalize(x,t);xs,seed,k=args;xs=list(map(n,xs));seed,k=n(seed),n(k);held='heldout' in name
    if staged:
        acc=0;prefix=[]
        for x in xs:acc=n(acc+x);prefix.append(acc)
    if 'first_value' in name:
        x=(prefix[0] if prefix else seed) if staged else (xs[0] if xs else seed)
        return n(n(x*k)+seed) if held else n(x+k)
    f=lambda x:(n(n(x*k)+seed) if x>k else n(seed-x)) if held else (n(x+k) if x<seed else n(x-seed))
    if not staged:return list(map(f,xs))
    pairs=zip(prefix,xs) if 'left_project' in name else zip(xs,prefix)
    return [f(b if 'left_project' in name else a) for a,b in pairs]

def frames(t):
    n=lambda x:normalize(x,t);bits=64 if t=='u64' else 32;hi=(1<<31)-1 if t=='i32' else (1<<bits)-1;lo=-(1<<31) if t=='i32' else 0;r=random.Random(2303)
    return [[[],n(7),n(-3)],[[n(1)],n(7),n(-3)],[[0,1,7,8,hi,lo],n(7),n(-3)],[[hi,hi,lo,1,0],n(0),hi],[[n(r.getrandbits(bits)) for _ in range(19)],n(r.getrandbits(bits)),n(r.getrandbits(bits))]]

class Pipeline23Tests(unittest.TestCase):
    def setUp(self):
        self.commands=[];archive=os.environ.get('INK_PIPELINE23_EVIDENCE')
        if archive:self.directory=Path(archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True);self.archive=True
        else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-pipeline23-');self.directory=Path(self.tmp.name);self.archive=False
    def tearDown(self):
        if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
        else:self.tmp.cleanup()
    def run_command(self,*args,success=True):
        r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
        if success:self.assertEqual(r.returncode,0,r.stderr)
        return r
    def test_novelty_and_symmetric_old_only_opportunity(self):
        from producers.beta_sharing17 import derive
        old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1648)
        support,roots=grouped_laws();self.assertEqual((len(support),len(roots)),(6,9));self.assertEqual(len(law_roles()),15)
        ids={identity(semantic_entry(v)) for _,v in named_laws()};self.assertFalse(ids&set(old.members()));endpoints={alpha_endpoints(v) for _,v in roots};generic=[]
        for oid in sorted(old.members()):
            obj=old.object(oid);p=dict(obj['payload'],schema=1,semantics=obj['semantics'],dependencies=obj['dependencies'])
            if all(k in p for k in ('params','from','to','proof')) and isinstance(p['from'],dict) and 'node' in p['from']:
                self.assertNotIn(alpha_endpoints(p),endpoints);generic.append(('prior_'+oid,p))
        records=[]
        for name,t,text in source_functions()+source_functions(True):
            if t!='u32':continue
            src=self.directory/(name+'.ink');src.write_text('module Prior23;\n'+text+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',sem);subject=json.loads(sem.read_text());rows=derive(subject,generic);attempts=[]
            for index,(candidate_name,candidate) in enumerate(rows):
                deps=old.bundle(candidate['dependencies'])['objects'];objects=list(deps.values())+[semantic_entry(candidate)]
                local=Store.publish(self.directory/(name+'-old-'+str(index)),objects,{candidate_name:identity(semantic_entry(candidate))});local.rebuild();view=local.root/'view.json';view.write_bytes(canonical(local.bundle([identity(semantic_entry(candidate))]))+b'\n');result=self.run_command(COMPILER,'knowledge-check',core,view,success=False);self.assertNotEqual(result.returncode,0,result.stdout);attempts.append(dict(name=candidate_name,id=identity(semantic_entry(candidate)),exit_code=result.returncode,stderr=result.stderr))
            records.append(dict(function=name,old_first_step_proposals=len(rows),old_admitted_first_steps=0,rejected=attempts,subject_sha256=hashlib.sha256(sem.read_bytes()).hexdigest()))
        (self.directory/'novelty.json').write_text(json.dumps(dict(prior=PIN,prior_entries=1648,old_semantic_laws=len(generic),roles=law_roles(),subjects=records,scope='Strict old beta-sharing opportunity; no first-step frontier for bounded composition. Parent independently stages fair full-catalogue selection.'),indent=2)+'\n')
    def test_admission_default_selection_replay_full_arrays_and_gpu_builds(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        rows=source_functions()+source_functions(True);src=self.directory/'all.ink';src.write_text('module Pipeline23;\n'+'\n'.join(r[2] for r in rows)+'\n');core=src.with_suffix('.core.json');sem=src.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',sem);subject=json.loads(sem.read_text());derived=specialize(subject);self.assertEqual(len(derived),18);st=publish(self.directory/'isolated',derived);self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json');apps=[];searches=[]
        for name,t,text in rows:
            unit=self.directory/(name+'.ink');unit.write_text('module Unit23;\n'+text+'\n');uc=unit.with_suffix('.core.json');sel=unit.with_suffix('.selection.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc)
            r=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',512,'--compact-output','-o',sel);searches.append(json.loads(r.stdout));selection=json.loads(sel.read_text());self.assertEqual(len(selection['applications']),1,(name,selection['applications']));apps+=selection['applications']
        sel=self.directory/'all.selection.json';sel.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');replay=self.run_command(COMPILER,'check-selection',core,sel);selected=self.directory/'selected.core.json';self.run_command(COMPILER,'emit-core',src,'--selection',sel,'-o',selected);out=selected.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-semantic',selected,'--core','-o',out);terms=json.loads(out.read_text())['functions'];records=[]
        for name,t,text in rows:
            enc=json.dumps(terms[name]);self.assertNotIn('method:scan',enc);self.assertNotIn('scan.acc',enc);self.assertNotIn('method:zip',enc)
            self.assertEqual(enc.count('method:map'),0 if 'first_value' in name else 1)
            for i,args in enumerate(frames(t)):
                p=self.directory/f'args-{t}-{i}.json';p.write_text(json.dumps(args)+'\n');before=json.loads(self.run_command(COMPILER,'run',src,name,p).stdout);after=json.loads(self.run_command(COMPILER,'run',selected,name,p,'--core').stdout);self.assertEqual(before,after);self.assertEqual(before,oracle(name,args,True));self.assertEqual(before,oracle(name,args,False));records.append(dict(function=name,type=t,arguments=args,original=before,selected=after))
        builds=[]
        for held in (False,True):
            group=[r for r in rows if r[1]=='u32' and 'first_value' not in r[0] and ('heldout' in r[0])==held];unit=self.directory/f'u32-{int(held)}-gpu.ink';unit.write_text('module Gpu23;\n'+'\n'.join(r[2] for r in group)+'\n');uc=unit.with_suffix('.core.json');us=unit.with_suffix('.semantic.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc);self.run_command(COMPILER,'emit-semantic',uc,'--core','-o',us);u=json.loads(us.read_text());ua=[a for a in apps if a['function'] in u['functions']];package=unit.with_suffix('.selection.json');package.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=u['input_core_sha256'],knowledge=st.bundle([a['law'] for a in ua]),applications=ua),separators=(',',':'))+'\n');self.run_command(COMPILER,'check-selection',uc,package);sc=unit.with_suffix('.selected.core.json');self.run_command(COMPILER,'emit-core',unit,'--selection',package,'-o',sc);bundle=self.directory/f'u32-{int(held)}-gpu';self.run_command(COMPILER,'build',sc,'--core','--target','webgpu','--zig',ROOT.parent.parent/'toolchain/zig-aarch64-macos-0.15.2/zig','-o',bundle);manifest=json.loads((bundle/'manifest.json').read_text());self.assertEqual(len(manifest['functions']),2)
            for fn in manifest['functions']:self.assertIsNotNone(fn.get('shader'));self.assertIsNone(fn.get('fallback_reason'));builds.append(dict(function=fn['name'],shader=fn['shader'],schema=manifest['schema']))
        (self.directory/'gpu-builds.json').write_text(json.dumps(dict(shaders=builds,gpu_calls=0),indent=2)+'\n');(self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'source-witnesses.json').write_text(json.dumps([dict(name=n,law=v) for n,v in derived],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(generic_roots=9,initial_state_supports=6,typed_source_witnesses=18,frames=len(records),interpreter_runs=2*len(records),replay=json.loads(replay.stdout),searches=searches),indent=2)+'\n')
    def test_arbitrary_initial_state_capture_safety_and_false_controls(self):
        src=self.directory/'unit.ink';src.write_text('module Controls23;\n'+source_functions()[0][2]+'\n');core=src.with_suffix('.core.json');self.run_command(COMPILER,'emit-core',src,'-o',core)
        s,ls=value('U32'),value({'List':'U32'});xs=var(ls,'xs');g=lam(s,op(s,'binary:+',bound(s,0),word('U32',7)));projection=lam(s,lam(s,op(s,'apply',g,bound(s,0))));data=term(ls,{'Cons':[word('U32',0xffffffff),term(ls,{'Cons':[word('U32',2),term(ls,'Nil')]})]})
        supports,roots=grouped_laws();rule=dict(roots)['scan_left_project_u32'];gid=identity(semantic_entry(rule))
        # Functional induction is over all accumulator values; the public rule
        # specializes initial0. Closed support transport witnesses exercise wrap.
        witnesses=[]
        from producers.beta_specialization15 import instantiate_bound
        from producers.beta_sharing17 import beta_share
        for initial in (7,0xffffffff):
            seq=op(ls,'scan.acc',data,word('U32',initial));left=op(ls,'method:zip',seq,data,projection);target=term(ls,{'Cons':[word('U32',6),term(ls,{'Cons':[word('U32',9),term(ls,'Nil')]})]});witness=law({},left,target);st=publish(self.directory/('initial-'+str(initial)),[('initial',witness)]);self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json');witnesses.append(dict(initial=initial,id=identity(semantic_entry(witness))))
        failures=[]
        bad=copy.deepcopy(rule);bad['params']['ys']=ls;bad['from']['node']['Op'][1][1]=var(ls,'ys');bad['proof']='Normalize'
        scalar=copy.deepcopy(dict(roots)['scan_first_value_u32']);scalar['from']['node']['Op'][1][1]=word('U32',1);scalar['to']['node']['Op'][1][1]=word('U32',1);scalar['proof']='Normalize'
        for label,v in [('wrong-receiver',bad),('second-prefix-is-not-second-element',scalar)]:
            st=publish(self.directory/label,[(label,v)]);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(label=label,id=identity(semantic_entry(v)),stderr=r.stderr))
        # A live prefix is never abstracted away by the specialization helper.
        live=lam(s,lam(s,op(s,'binary:+',bound(s,1),bound(s,0))));term_=op(ls,'method:zip',op(ls,'method:scan',xs),xs,live);self.assertEqual(specialize(dict(functions={'unrelated_name':term_})),[])
        # Nested lambda-local x binding plus captured free threshold is safe.
        nested=lam(s,lam(s,op(s,'apply',lam(s,op(s,'binary:+',bound(s,0),var(s,'captured'))),bound(s,0))));original=op(ls,'method:zip',op(ls,'method:scan',xs),xs,nested);rows=specialize(dict(functions={'arbitrary_export':original}));self.assertEqual(len(rows),2);self.assertEqual(sum('method:scan' not in json.dumps(v['to']) for _,v in rows),1);st=publish(self.directory/'capture',rows);self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json')
        self.assertNotEqual([16],[8,9]);self.assertNotEqual((1+2)&0xffffffff,2)
        (self.directory/'controls.json').write_text(json.dumps(dict(initial_state_witnesses=witnesses,false_controls=failures,counterexamples=dict(wrong_receiver=dict(xs=[1,2],ys=[9],source=[16],false_target=[8,9]),second_prefix=dict(xs=[1,2],source=3,false_target=2)),nested_captured_callback_checked=True,live_prefix_rejected=True),indent=2)+'\n')

if __name__=='__main__':unittest.main()
