"""Minimal checked closures for arbitrary wrapping permutation consumers."""
import hashlib,json,os,random,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import binary,word
from producers.web_permutation18_laws import named_laws,publish,source_functions
ROOT=Path(__file__).resolve().parents[1]
COMPILER=ROOT.parent.parent/'toolchain/ink-sequence-proofs'
PIN='717bc5be3b6d186678d71d3c11ec5a10a0bdc884759993f1d70add7a37b20c76'


def alpha_endpoints(candidate):
    names={}
    def walk(v):
        if isinstance(v,dict):
            if set(v)=={'Free'}:
                if v['Free'] not in names:names[v['Free']]='v'+str(len(names))
                return {'Free':names[v['Free']]}
            return {k:walk(v[k]) for k in sorted(v)}
        if isinstance(v,list):return [walk(x) for x in v]
        return v
    return canonical(walk([candidate['from'],candidate['to']]))


def wrap(v,t):
    bits=64 if t=='u64' else 32;v&=(1<<bits)-1
    return v-(1<<32) if t=='i32' and v>=1<<31 else v


def contribution(x,seed,k,t,recipe):
    n=lambda v:wrap(v,t)
    if recipe=='sorted_calibrated_total':return n(n(x*3)+k)
    if recipe=='sorted_squared_energy':return n(n(x*x)+k)
    if recipe=='sorted_distance_total':return n(seed-x) if x<seed else n(x-seed)
    if recipe=='sorted_calibrated_total_heldout':return n(x*k) if x<seed else n(x+k)
    if recipe=='sorted_squared_energy_heldout':return n(n(x-seed)*n(x-seed))
    if recipe=='sorted_distance_total_heldout':return x if x<seed else seed
    raise KeyError(recipe)


def oracle(args,t,recipe,ordered):
    xs,seed,k=args
    if recipe=='count':return len(xs)
    values=[contribution(x,seed,k,t,recipe) for x in sorted(xs)] if ordered else [contribution(x,seed,k,t,recipe) for x in xs]
    total=0
    for x in values:total=wrap(total+x,t)
    return total


def frames(t):
    bits=64 if t=='u64' else 32;high=(1<<31)-1 if t=='i32' else (1<<bits)-1;low=-(1<<31) if t=='i32' else 0
    rng=random.Random(1807)
    random_xs=[wrap(rng.getrandbits(bits),t) for _ in range(16)]
    return [[[],7,wrap(-3,t)],[[high],7,high],[[high,low,1,0,high],7,wrap(-3,t)],
        [[wrap(v,t) for v in [9,7,3,1,0,-1]],3,7],[[low,1,1,high,0,low],low,high],
        [random_xs,wrap(rng.getrandbits(bits),t),wrap(rng.getrandbits(bits),t)],
        [sorted(random_xs),7,3]]


class Permutation18Tests(unittest.TestCase):
    def setUp(self):
        self.commands=[];self.archive=os.environ.get('INK_PERMUTATION18_EVIDENCE')
        if self.archive:self.directory=Path(self.archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
        else:self.temp=tempfile.TemporaryDirectory(prefix='ink-permutation18-');self.directory=Path(self.temp.name)
    def tearDown(self):
        if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
        else:self.temp.cleanup()
    def run_command(self,*args,success=True):
        argv=list(map(str,args));r=subprocess.run(argv,text=True,capture_output=True)
        self.commands.append(dict(argv=argv,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
        if success:self.assertEqual(r.returncode,0,r.stderr)
        return r
    def test_alpha_novelty_and_explicit_insertion_dependencies(self):
        old=Store(ROOT,ROOT/'store/snapshots'/f'{PIN}.json');self.assertEqual(len(old.members()),1247)
        laws=named_laws();ids={identity(semantic_entry(v)) for _,v in laws};self.assertEqual(len(ids),12);self.assertFalse(ids&set(old.members()))
        endpoints={alpha_endpoints(v) for _,v in laws}
        duplicates=[]
        for i in old.members():
            p=old.object(i)['payload']
            if 'from' in p and 'node' in p['from'] and alpha_endpoints(p) in endpoints:duplicates.append(i)
        self.assertEqual(duplicates,[])
        for name,v in laws:self.assertEqual(len(v['dependencies']),1 if name.startswith('sorted_') else 0)
        (self.directory/'novelty.json').write_text(json.dumps(dict(baseline_snapshot=PIN,baseline_entries=1247,names={n:identity(semantic_entry(v)) for n,v in laws},alpha_duplicates=duplicates),indent=2)+'\n')
    def test_admission_default_selection_replay_reification_and_typed_outputs(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        store=publish(self.directory/'generic');rows=source_functions();source=self.directory/'typed.ink';source.write_text('module Permutation18;\n'+'\n'.join(r[3] for r in rows)+'\n')
        core=self.directory/'typed.core.json';subject=self.directory/'typed.semantic.json';self.run_command(COMPILER,'emit-core',source,'-o',core);self.run_command(COMPILER,'knowledge-check',core,store.root/'view.json');self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject)
        original=json.loads(subject.read_text());apps=[];searches=[]
        laws=dict(named_laws())
        for name,t,recipe,text in rows:
            unit=self.directory/(name+'.ink');unit.write_text('module Permutation18Unit;\n'+text+'\n');uc=unit.with_suffix('.core.json');out=unit.with_suffix('.selection.json')
            self.run_command(COMPILER,'emit-core',unit,'-o',uc)
            receipt=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',uc,'--knowledge-root',store.root,'--snapshot',store.data/'snapshot.json','--budget',128,'-o',out)
            searches.append(json.loads(receipt.stdout));selected=json.loads(out.read_text())['applications'];self.assertEqual(len(selected),1)
            expected='sorted_count_'+t if recipe=='count' else 'sorted_mapped_sum_'+t
            self.assertEqual(selected[0]['law'],identity(semantic_entry(laws[expected])));apps+=selected
        selection=self.directory/'typed.selection.json';selection.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=original['input_core_sha256'],knowledge=store.bundle(sorted({a['law'] for a in apps})),applications=apps),separators=(',',':'))+'\n')
        replay=self.run_command(COMPILER,'check-selection',core,selection)
        selected_core=self.directory/'selected.core.json';self.run_command(COMPILER,'emit-core',source,'--selection',selection,'-o',selected_core)
        semantic=self.directory/'selected.semantic.json';self.run_command(COMPILER,'emit-semantic',selected_core,'--core','-o',semantic);terms=json.loads(semantic.read_text())['functions']
        for name,t,recipe,text in rows:
            self.assertNotIn('method:sort',json.dumps(terms[name]));self.assertNotIn('list.insert',json.dumps(terms[name]));self.assertNotEqual(terms[name],original['functions'][name])
        argfiles={}
        for t in ['u32','i32','u64']:
            argfiles[t]=[]
            for i,args in enumerate(frames(t)):
                p=self.directory/f'args-{t}-{i}.json';p.write_text(json.dumps(args)+'\n');argfiles[t].append((p,args))
        results=[]
        for name,t,recipe,text in rows:
            for path,args in argfiles[t]:
                literal=oracle(args,t,recipe,True);unsorted=oracle(args,t,recipe,False);self.assertEqual(literal,unsorted)
                before=json.loads(self.run_command(COMPILER,'run',source,name,path).stdout);after=json.loads(self.run_command(COMPILER,'run',selected_core,name,path,'--core').stdout)
                self.assertEqual(before,literal);self.assertEqual(after,literal);results.append(dict(function=name,type=t,recipe=recipe,arguments=args,original=before,selected=after,oracle=literal))
        (self.directory/'interpreter-results.json').write_text(json.dumps(results,indent=2)+'\n')
        (self.directory/'scope.json').write_text(json.dumps(dict(searches=searches,applications=apps,replay=json.loads(replay.stdout),typed_frames=len(results),actual_runs=2*len(results),oracle='Eager integer sort/map/sum versus unsorted map/sum; exact modular primitives. <=16 elements. Count U64 high lane not physically exercised.'),indent=2)+'\n')
    def test_hash_valid_false_missing_contribution_and_wrong_count_rejected(self):
        source=self.directory/'source.ink';source.write_text('module Negative18;\n'+source_functions()[0][3]+'\n');core=self.directory/'source.core.json';self.run_command(COMPILER,'emit-core',source,'-o',core)
        cases=[];named=dict(named_laws())
        missing=json.loads(json.dumps(named['insert_mapped_sum_contribution_u32']));missing['to']=missing['to']['node']['Op'][1][1];cases.append(('missing-contribution',missing))
        badcount=json.loads(json.dumps(named['sorted_count_u64']));badcount['to']=binary('+',badcount['to'],word('U64',1));cases.append(('wrong-count',badcount))
        for name,candidate in cases:
            bad=semantic_entry(candidate);store=Store.publish(self.directory/name,[semantic_entry(v) for _,v in named_laws()]+[bad]);view=self.directory/name/'view.json';view.write_bytes(canonical(store.bundle([identity(bad)]))+b'\n')
            r=self.run_command(COMPILER,'knowledge-check',core,view,success=False);self.assertNotEqual(r.returncode,0);self.assertNotIn('identity mismatch',r.stderr);self.assertIn('semantic normal forms differ',r.stderr)

if __name__=='__main__':unittest.main()
