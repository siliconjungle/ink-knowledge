"""Generic direct paired fusion and independently checked source deployments."""
import copy,hashlib,json,math,os,random,struct,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import bound,lam,op,value,word,binary
from producers.web_algebra19_laws import named_laws,publish,source_functions,specialize
ROOT=Path(__file__).resolve().parents[1]
COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs'
PIN='44da9d5032f213c6458bbce156792a47187568aad56af44e3b5832993ede70a5'
COST=ROOT.parent/'reports/web-stack-proofs-18-2026-10-11/cpu-cost-model.json'


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


def oracle(args,t,heldout,eager):
    xs,seed,k=args;xs=list(map(number,xs));seed,k=number(seed),number(k);n=lambda v:normalize(v,t)
    if heldout:
        f=lambda x:x if x>k else seed;r=lambda x:seed if x>k else x
        g=lambda a,b:n(n(a*b)+seed) if a>b else n(a+n(b*k))
    else:
        f=lambda x:x if x<seed else k;r=lambda x:k if x<seed else x
        g=lambda a,b:n(a+n(b*k)) if a<b else n(a-n(b*k))
    if eager:return [g(a,b) for a,b in zip([f(x) for x in xs],[r(x) for x in xs])]
    return [g(f(x),r(x)) for x in xs]


def frames(t):
    rng=random.Random(1907)
    if t=='f32':
        special=[{'F32Bits':0x7fc00123},{'F32Bits':0x7f800000},{'F32Bits':0xff800000},0.0,-0.0]
        rows=[[[],2.0,3.0],[[0.0,-0.0,1.0,2.0,3.0,8.0],2.0,3.0],[special,2.0,-3.0],
              [[0.0,-0.0,1.0,-1.0],{'F32Bits':0x7fc00000},2.0],
              [[0.0,-0.0,1.0,-1.0],2.0,{'F32Bits':0x7fc00000}],
              [[0.0,-0.0,1.0,-1.0],-0.0,{'F32Bits':0x7f800000}],
              [[1e20,-1e20,1.5,-2.0],-2.0,1e20]]
        rows.append([[rng.randrange(-1000,1000)/8 for _ in range(31)],17.25,-3.0]);return rows
    bits=64 if t=='u64' else 32;high=(1<<31)-1 if t=='i32' else (1<<bits)-1;low=-(1<<31) if t=='i32' else 0
    return [[[],7,normalize(-3,t)],[[0,1,7,8,63,127,high,low],63,7],
            [[high,low,high,1,0],7,normalize(-3,t)],[[1,2,3,4,5],3,high],
            [[normalize(rng.getrandbits(bits),t) for _ in range(31)],normalize(rng.getrandbits(bits),t),normalize(rng.getrandbits(bits),t)]]


class Algebra19Tests(unittest.TestCase):
    def setUp(self):
        self.commands=[];self.archive=os.environ.get('INK_ALGEBRA19_EVIDENCE')
        if self.archive:self.directory=Path(self.archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
        else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-algebra19-');self.directory=Path(self.tmp.name)
    def tearDown(self):
        if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
        else:self.tmp.cleanup()
    def run_command(self,*args,success=True):
        r=subprocess.run(list(map(str,args)),capture_output=True,text=True);self.commands.append(dict(argv=list(map(str,args)),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
        if success:self.assertEqual(r.returncode,0,r.stderr)
        return r
    def test_four_alpha_fresh_generic_roots(self):
        old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1298)
        named=named_laws();ids={identity(semantic_entry(v)) for _,v in named};self.assertEqual(len(ids),4);self.assertFalse(ids&set(old.members()))
        endpoints={alpha_endpoints(v) for _,v in named}
        for oid in old.members():
            p=old.object(oid)['payload']
            if isinstance(p.get('from'),dict) and 'node' in p['from']:self.assertNotIn(alpha_endpoints(p),endpoints)
        self.assertTrue(all(set(v['params'])=={'xs','f','r','h'} and not v['dependencies'] for _,v in named))
        (self.directory/'novelty.json').write_text(json.dumps(dict(baseline_snapshot=PIN,baseline_entries=1298,names={n:identity(semantic_entry(v)) for n,v in named}),indent=2)+'\n')
    def test_checked_sharing_deployment_and_complete_typed_arrays(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        rows=source_functions()+source_functions(True);src=self.directory/'typed.ink';src.write_text('module Algebra19Typed;\n'+'\n'.join(r[2] for r in rows)+'\n');core=self.directory/'typed.core.json';subject=self.directory/'typed.semantic.json'
        self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject);original=json.loads(subject.read_text());derived=specialize(original);self.assertEqual(len(derived),8);st=publish(self.directory/'isolated',derived);self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json')
        apps=[];searches=[]
        for name,t,text in rows:
            unit=self.directory/(name+'.ink');unit.write_text('module Unit19;\n'+text+'\n');uc=unit.with_suffix('.core.json');out=unit.with_suffix('.selection.json');self.run_command(COMPILER,'emit-core',unit,'-o',uc)
            r=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',st.root,'--snapshot',st.data/'snapshot.json','--cost-model',COST,'--budget',512,'-o',out);searches.append(json.loads(r.stdout));selection=json.loads(out.read_text());self.assertEqual(len(selection['applications']),1);apps+=selection['applications']
        sel=self.directory/'all.selection.json';sel.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=original['input_core_sha256'],knowledge=st.bundle([a['law'] for a in apps]),applications=apps),separators=(',',':'))+'\n');replay=self.run_command(COMPILER,'check-selection',core,sel);selected=self.directory/'selected.core.json';self.run_command(COMPILER,'emit-core',src,'--selection',sel,'-o',selected)
        after_sem=self.directory/'selected.semantic.json';self.run_command(COMPILER,'emit-semantic',selected,'--core','-o',after_sem);after_terms=json.loads(after_sem.read_text())['functions'];records=[]
        for name,t,text in rows:
            term=after_terms[name];self.assertEqual(json.dumps(term).count('method:map'),1);self.assertNotIn('method:zip',json.dumps(term));self.assertNotIn('__beta_share_',json.dumps(term))
            for index,args in enumerate(frames(t)):
                path=self.directory/f'args-{t}-{index}.json';path.write_text(json.dumps(args)+'\n');eager=oracle(args,t,'heldout' in name,True);streamed=oracle(args,t,'heldout' in name,False)
                before=json.loads(self.run_command(COMPILER,'run',src,name,path).stdout);after=json.loads(self.run_command(COMPILER,'run',selected,name,path,'--core').stdout);self.assertEqual(before,after);self.assertEqual(len(before),len(args[0]))
                for a,b,actual in zip(eager,streamed,before):
                    if t=='f32':
                        actual=number(actual)
                        if math.isnan(a):self.assertTrue(math.isnan(b) and math.isnan(actual))
                        else:self.assertEqual(struct.pack('<f',a),struct.pack('<f',b));self.assertEqual(struct.pack('<f',a),struct.pack('<f',actual))
                    else:self.assertEqual(a,b);self.assertEqual(a,actual)
                records.append(dict(function=name,type=t,arguments=args,original=before,selected=after))
        (self.directory/'interpreter-results.json').write_text(json.dumps(records,indent=2)+'\n');(self.directory/'sharing-witnesses.json').write_text(json.dumps([dict(name=n,law=v) for n,v in derived],indent=2)+'\n');(self.directory/'scope.json').write_text(json.dumps(dict(generic_roots=4,checked_callback_instances=8,typed_frames=len(records),actual_interpreter_runs=2*len(records),replay=json.loads(replay.stdout),searches=searches),indent=2)+'\n')
    def test_hash_valid_false_swapped_operands_and_wrong_output_rejected(self):
        src=self.directory/'negative.ink';src.write_text('module Negative19;\n'+source_functions()[0][2]+'\n');core=self.directory/'negative.core.json';subject=self.directory/'negative.semantic.json';self.run_command(COMPILER,'emit-core',src,'-o',core);self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject)
        generic=named_laws();derived=specialize(json.loads(subject.read_text()));bad=copy.deepcopy(generic[0][1]);body=bad['to']['node']['Op'][1][1]['node']['Lambda'];args=body['node']['Op'][1];inner=args[0]['node']['Op'][1];inner[1],args[1]=args[1],inner[1]
        bad2=copy.deepcopy(derived[0][1]);s=value('U32');ls=value({'List':'U32'});bad2['to']=op(ls,'method:map',bad2['to'],lam(s,binary('+',bound(s,0),word('U32',1))))
        failures=[]
        for label,v in [('swapped',bad),('wrong-output',bad2)]:
            st=publish(self.directory/label,derived+[(label,v)]);r=self.run_command(COMPILER,'knowledge-check',core,st.root/'view.json',success=False);self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr);failures.append(dict(label=label,content_id=identity(semantic_entry(v)),stderr=r.stderr))
        (self.directory/'false-controls.json').write_text(json.dumps(failures,indent=2)+'\n')

if __name__=='__main__':unittest.main()
