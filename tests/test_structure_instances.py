"""Structure laws are proved once; each program instance is checked by the kernel."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store
from ink_knowledge.structure_instances import beta,witnesses,equality_witness,generate
from producers.structure_laws import publish,permutation_laws,check
from ink_knowledge.store import semantic_entry,identity
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
ABSORBING='''module absorbing;
pub fn all_below(xs:List<u32>,cut:u32)->Bool{return foldl(xs,true,fn(x)=>fn(a)=>a && x<cut);}
pub fn any_above(xs:List<u32>,cut:u32)->Bool{return foldl(xs,false,fn(x)=>fn(a)=>a || x>cut);}
pub fn product(xs:List<u64>,k:u64)->u64{return foldl(xs,1,fn(x)=>fn(a)=>a*(x+k));}
pub fn total(xs:List<u32>)->u32{return foldl(xs,0,fn(x)=>fn(a)=>a+x);}
'''
SORTED='''module sorted;
pub fn total_sorted(xs:List<u32>)->u32{return foldr(xs.sort(),0,fn(x)=>fn(a)=>x+a);}
pub fn count_big(xs:List<u32>,k:u32)->u64{return foldr(xs.sort(),0,fn(x)=>fn(a)=>choose(x>k,a+1,a));}
pub fn rebuilt(xs:List<u32>)->List<u32>{return foldr(xs.sort(),[],fn(x)=>fn(a)=>[x].concat(a));}
'''

EXTREMA='''module extrema;
pub fn largest(xs:List<u32>)->u32{return foldr(xs.sort(),0,fn(x)=>fn(a)=>choose(x>a,x,a));}
pub fn smallest(xs:List<u64>,z:u64)->u64{return foldr(xs.sort(),z,fn(x)=>fn(a)=>choose(x<a,x,a));}
pub fn clamped(xs:List<u32>,cap:u32)->u32{return foldr(xs.sort(),0,fn(x)=>fn(a)=>choose(x>a,choose(x>cap,choose(a>cap,a,cap),x),a));}
pub fn first_item(xs:List<u32>)->u32{return foldr(xs.sort(),0,fn(x)=>fn(a)=>x);}
pub fn signed_max(xs:List<i32>)->i32{return foldr(xs.sort(),0,fn(x)=>fn(a)=>choose(x>a,x,a));}
'''

def word(n):return dict(sort={'Value':'U32'},node={'Word':n})

class Heuristics(unittest.TestCase):
    def test_beta_exposes_step_bodies(self):
        u={'Value':'U32'};body=dict(sort=u,node={'Op':['binary:+',[dict(sort=u,node={'Bound':0}),word(1)]]})
        redex=dict(sort=u,node={'Op':['apply',[dict(sort={'Arrow':[u,u]},node={'Lambda':body}),word(4)]]})
        self.assertEqual(beta(redex),dict(sort=u,node={'Op':['binary:+',[word(4),word(1)]]}))
    def test_witnesses_are_small_and_typed(self):
        predicates=witnesses({'Arrow':[{'Value':'Bool'},{'Value':'Bool'}]},word(0))
        self.assertEqual(len(predicates),2)
        site=dict(sort={'Value':'U32'},node={'Op':['binary:*',[word(7),word(0)]]})
        values=[w['node']['Word'] for w in witnesses({'Value':'U32'},site)]
        self.assertEqual(values,[0,7])
        self.assertEqual(witnesses({'Value':'String'},word(0)),[])
        applied=dict(sort={'Value':'Bool'},node={'Op':['apply',[predicates[0],dict(sort={'Value':'Bool'},node={'Free':'t'})]]})
        self.assertEqual(equality_witness(applied)[1]['node'],{'Bool':False})

class KernelInstances(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory();d=Path(cls.temporary.name)
        Store.publish(d/'knowledge',[]);(d/'knowledge/store/names.json').write_text('{}')
        cls.receipt=publish(COMPILER,d/'knowledge');cls.store=Store(d/'knowledge');cls.dir=d
    @classmethod
    def tearDownClass(cls):cls.temporary.cleanup()
    def instances(self,source):
        d=Path(tempfile.mkdtemp(dir=self.dir));path=d/'p.ink';path.write_text(source)
        core=d/'core.json';subject=d/'subject.json'
        for args in [['emit-core',path,'-o',core],['emit-semantic',core,'--core','-o',subject]]:
            r=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True);self.assertEqual(r.returncode,0,r.stderr)
        subject=json.loads(subject.read_text());objects,receipt=generate(self.store,subject,json.loads(core.read_text()),COMPILER)
        sites={}
        for name,body in subject['functions'].items():
            from ink_planner.semantic_search import positions
            for _,t in positions(body):sites.setdefault(json.dumps(t,sort_keys=True),name)
        return {sites[json.dumps(o['payload']['from'],sort_keys=True)] for o in objects.values()},receipt,objects
    def test_library_publishes_general_laws_only(self):
        self.assertIn('absorbing_foldl',self.receipt['laws']);self.assertIn('fold_sort_u32',self.receipt['laws'])
        for name in self.receipt['laws']:
            obj=self.store.object(json.loads((self.dir/'knowledge/store/names.json').read_text())['structure-laws/'+name])
            self.assertEqual(obj['semantics'],'ink-general-laws-v1');self.assertTrue(obj['payload']['assumptions'])
    def test_absorbing_states_are_found_only_where_they_exist(self):
        functions,receipt,objects=self.instances(ABSORBING)
        self.assertEqual(functions,{'all_below','any_above','product'})
        self.assertEqual(receipt['admitted'],3)
        for obj in objects.values():self.assertEqual(obj['payload']['to']['node']['Op'][0],'call:fold_until')
    def test_sorting_is_erased_only_before_commuting_steps(self):
        functions,receipt,_=self.instances(SORTED)
        self.assertEqual(functions,{'total_sorted','count_big'})
    def test_extrema_steps_commute_by_order_analysis(self):
        # Maxima, minima and a clamped maximum need transitivity of the
        # comparison, which only the kernel's order analysis supplies; a step
        # that keeps the first item does not commute and stays rejected.
        functions,receipt,objects=self.instances(EXTREMA)
        self.assertEqual(functions,{'largest','smallest','clamped','signed_max'})
        used=json.dumps(sorted(objects.values(),key=json.dumps))
        self.assertIn('"Order"',used)
    def test_broken_library_proofs_are_rejected(self):
        lemma=copy.deepcopy(dict(permutation_laws())['insert_fold_u32'])
        lemma['proof']['Induction']['step']['Cases']['on_false']='Normalize'
        entry=semantic_entry(lemma)
        with self.assertRaises(ValueError):check(COMPILER,{identity(entry):entry},[identity(entry)])
    def test_without_a_compiler_nothing_is_proposed(self):
        objects,receipt=generate(self.store,{'functions':{}},{'program':{'functions':[]}},None)
        self.assertEqual(objects,{});self.assertTrue(receipt['skipped'])

if __name__=='__main__':unittest.main()
