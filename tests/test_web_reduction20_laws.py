"""Novel endpoints, checked deployment and independent ordered/full-array oracles."""
import copy,hashlib,json,math,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import binary,word
from producers.web_reduction20_laws import named_laws,fold_laws,composed_zip_laws,dependency_objects,publish,source_functions,vector_source_functions,specialize
ROOT=Path(__file__).resolve().parents[1]
COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs'
PIN='6f99dae6d3ca740006f5840d179e17afcb43c5a99c34b5ffb1c02b73d207b177'
COST=ROOT.parent/'reports/web-stack-proofs-19-2026-10-11/cpu-cost-model.json'

def alpha_endpoints(candidate):
    names={}
    def visit(v):
        if isinstance(v,dict):
            if set(v)=={'Free'}:
                n=v['Free'];names.setdefault(n,'v'+str(len(names)));return {'Free':names[n]}
            return {k:visit(v[k]) for k in sorted(v)}
        if isinstance(v,list):return [visit(x) for x in v]
        return v
    return canonical(visit([candidate['from'],candidate['to']]))

def number(v):return struct.unpack('<f',struct.pack('<I',v['F32Bits']))[0] if isinstance(v,dict) else v

def normalize(v,t):
    if t=='f32':
        try:return struct.unpack('<f',struct.pack('<f',v))[0]
        except OverflowError:return math.copysign(math.inf,v)
    bits=64 if t=='u64' else 32;v&=(1<<bits)-1
    return v-(1<<32) if t=='i32' and v>=1<<31 else v

def oracle(args,t,heldout,vector,staged=True,reverse=True):
    n=lambda v:normalize(v,t)
    if vector:
        xs,ys,seed,k=args;xs=list(map(number,xs));ys=list(map(number,ys));seed,k=number(seed),number(k)
        h=(lambda a,b:n(a-b) if a>b else n(b-a)) if heldout else (lambda a,b:n(a+n(b*k)) if a<seed else n(a-n(b*k)))
        g=(lambda v:n(v*k) if v<seed else n(v+seed)) if heldout else (lambda v:n(v-seed) if v>k else n(v+seed))
        return [g(v) for v in [h(a,b) for a,b in zip(xs,ys)]] if staged else [g(h(a,b)) for a,b in zip(xs,ys)]
    xs,seed,k=args;xs=list(map(number,xs));seed,k=number(seed),number(k)
    h=(lambda a,b:n(n(a*b)+seed) if a>k else n(a+n(b*k))) if heldout else (lambda a,b:n(a+n(b*k)) if a<seed else n(a-n(b*k)))
    g=(lambda v,a:n(v+n(a*k)) if v<seed else n(v-a)) if heldout else (lambda v,a:n(v-a) if a<seed else n(v+n(a*k)))
    acc=seed
    if staged:
        values=[h(x,x) for x in xs]
        for v in reversed(values) if reverse else values:acc=g(v,acc)
    else:
        for x in reversed(xs) if reverse else xs:acc=g(h(x,x),acc)
    return acc

def frames(t,vector):
    rng=random.Random(20201011)
    if t=='f32':
        special=[{'F32Bits':0x7fc00123},{'F32Bits':0x7f800000},{'F32Bits':0xff800000},0.0,-0.0]
        base=[[[],2.0,3.0],[[0.0,-0.0,1.0,2.0,3.0,8.0],2.0,3.0],[special,2.0,-3.0],
              [[0.0,-0.0,1.0,-1.0],{'F32Bits':0x7fc00000},2.0],[[0.0,-0.0,1.0,-1.0],2.0,{'F32Bits':0x7fc00000}],
              [[0.0,-0.0,1.0,-1.0],-0.0,{'F32Bits':0x7f800000}],[[1e20,-1e20,1.5,-2.0],-2.0,1e20],
              [[rng.randrange(-1000,1000)/8 for _ in range(13)],17.25,-3.0]]
        ys=[[],[3.0,-0.0,4.0],special,[1.0,2.0],[-0.0,3.0],[1.0],[-1e20,1e20],[-4.0,3.0,8.0,1.0,2.0]]
    else:
        bits=64 if t=='u64' else 32;hi=(1<<31)-1 if t=='i32' else (1<<bits)-1;lo=-(1<<31) if t=='i32' else 0
        base=[[[],7,normalize(-3,t)],[[0,1,7,8,63,127,hi,lo],63,7],[[hi,lo,hi,1,0],7,normalize(-3,t)],[[1,2,3,4,5],3,hi],
              [[normalize(rng.getrandbits(bits),t) for _ in range(13)],normalize(rng.getrandbits(bits),t),normalize(rng.getrandbits(bits),t)]]
        ys=[[],[hi,lo,7],[0,1,hi,lo,3,4,5],[],[normalize(rng.getrandbits(bits),t) for _ in range(7)]]
    if not vector:return base
    result=[[x,y,s,k] for (x,s,k),y in zip(base,ys)]
    result.extend([[[],ys[-1],base[-1][1],base[-1][2]],[base[-1][0],[],base[-1][1],base[-1][2]]]);return result

class Reduction20Tests(unittest.TestCase):
    def setUp(self):
        self.commands=[];self.archive=os.environ.get('INK_REDUCTION20_EVIDENCE')
        if self.archive:self.directory=Path(self.archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
        else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-reduction20-');self.directory=Path(self.tmp.name)
    def tearDown(self):
        if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
        else:self.tmp.cleanup()
    def run_command(self,*args,success=True):
        r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
        if success:self.assertEqual(r.returncode,0,r.stderr)
        return r
    def test_eight_alpha_fresh_endpoints_and_explicit_composed_dependencies(self):
        old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1343)
        named=named_laws();ids={identity(semantic_entry(v)) for _,v in named};self.assertEqual(len(ids),8);self.assertFalse(ids&set(old.members()))
        endpoints={alpha_endpoints(v) for _,v in named}
        for oid in old.members():
            p=old.object(oid)['payload']
            if isinstance(p.get('from'),dict) and 'node' in p['from']:self.assertNotIn(alpha_endpoints(p),endpoints)
        self.assertTrue(all(not v['dependencies'] for _,v in fold_laws()));self.assertTrue(all(len(v['dependencies'])==2 for _,v in composed_zip_laws()))
        self.assertTrue({identity(e) for e in dependency_objects()}<=set(old.members()))
        (self.directory/'novelty.json').write_text(json.dumps(dict(baseline_snapshot=PIN,baseline_entries=1343,new_generic_fold=4,composed_existing_math_zip_endpoints=4,names={n:identity(semantic_entry(v)) for n,v in named}),indent=2)+'\n')
    def test_checked_sharing_selection_and_complete_typed_outputs(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        rows=[r for alt in [False,True] for r in source_functions(alt)+vector_source_functions(alt)];src=self.directory/'typed.ink';src.write_text('module Reduction20Typed;\n'+'\n'.join(r[2] for r in rows)+'\n');core=self.directory/'typed.core.json';sem=self.directory/'typed.semantic.json'
        self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',sem);original=json.loads(sem.read_text());derived=specialize(original);self.assertEqual(len(derived),16);st=publish(self.directory/'isolated',derived);self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json');apps=[];searches=[]
        for name,t,text in rows:
            unit=self.directory/(name+'.ink');unit.write_text('module Unit20;\n'+text+'\n');uc=unit.with_suffix('.core.json');sel=unit.with_suffix('.selection.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc)
            r=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',512,'--compact-output','-o',sel);searches.append(json.loads(r.stdout));selection=json.loads(sel.read_text());self.assertEqual(len(selection['applications']),1,(name,selection['applications']));apps+=selection['applications']
        sel=self.directory/'all.selection.json';sel.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=original['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');replay=self.run_command(COMPILER,'check-selection',core,sel);selected=self.directory/'selected.core.json';self.run_command(COMPILER,'emit-core',src,'--selection',sel,'-o',selected)
        after_sem=self.directory/'selected.semantic.json';self.run_command(COMPILER,'emit-semantic',selected,'--core','-o',after_sem);terms=json.loads(after_sem.read_text())['functions'];records=[];reversed_controls=[]
        for name,t,text in rows:
            vector=name.startswith('paired_calibrated_') or name.startswith('paired_contrast_');heldout='heldout' in name;term=json.dumps(terms[name]);self.assertNotIn('method:map',term)
            self.assertEqual(term.count('method:zip'),1 if vector else 0);self.assertEqual(term.count('call:foldr'),0 if vector else 1)
            for index,args in enumerate(frames(t,vector)):
                p=self.directory/f'args-{name}-{index}.json';p.write_text(json.dumps(args)+'\n');expected=oracle(args,t,heldout,vector);stream=oracle(args,t,heldout,vector,False)
                before=json.loads(self.run_command(COMPILER,'run',src,name,p).stdout);after=json.loads(self.run_command(COMPILER,'run',selected,name,p,'--core').stdout);self.assertEqual(before,after)
                av=before if vector else [before];ev=expected if vector else [expected];sv=stream if vector else [stream]
                if vector:self.assertEqual(len(av),min(len(args[0]),len(args[1])))
                for a,b,actual in zip(ev,sv,av):
                    if t=='f32':
                        actual=number(actual)
                        if math.isnan(a):self.assertTrue(math.isnan(b) and math.isnan(actual))
                        else:self.assertEqual(struct.pack('<f',a),struct.pack('<f',b));self.assertEqual(struct.pack('<f',a),struct.pack('<f',actual))
                    else:self.assertEqual(a,b);self.assertEqual(a,actual)
                if not vector and t=='u32':
                    wrong=oracle(args,t,heldout,False,True,False)
                    if expected!=wrong:reversed_controls.append(dict(name=name,arguments=args,correct=expected,forward=wrong))
                records.append(dict(function=name,type=t,arguments=args,original=before,selected=after))
        self.assertTrue(any(not ('heldout' in r['name']) for r in reversed_controls));self.assertTrue(any('heldout' in r['name'] for r in reversed_controls))
        (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'reversed-order-controls.json').write_text(json.dumps(reversed_controls,indent=2)+'\n');(self.directory/'sharing-witnesses.json').write_text(json.dumps([dict(name=n,law=v) for n,v in derived],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(roots=8,checked_callback_instances=16,typed_frames=len(records),actual_interpreter_runs=2*len(records),replay=json.loads(replay.stdout),searches=searches),indent=2)+'\n')
    def test_hash_valid_false_initial_accumulator_and_swapped_zip_rejected(self):
        src=self.directory/'negative.ink';src.write_text('module Negative20;\n'+source_functions()[0][2]+'\n');core=src.with_suffix('.core.json');self.run_command(COMPILER,'emit-core',src,'-o',core)
        first=copy.deepcopy(fold_laws()[0][1]);a=first['to']['node']['Op'][1];a[1]=binary('+',a[1],word('U32',1))
        second=copy.deepcopy(composed_zip_laws()[0][1]);args=second['to']['node']['Op'][1];args[0],args[1]=args[1],args[0]
        failures=[]
        for label,v in [('wrong-initial',first),('swapped-independent-inputs',second)]:
            st=publish(self.directory/label,[(label,v)]);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(label=label,content_id=identity(semantic_entry(v)),stderr=r.stderr))
        (self.directory/'false-controls.json').write_text(json.dumps(failures,indent=2)+'\n')

if __name__=='__main__':unittest.main()
