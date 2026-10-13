"""Context binding must not orphan the laws a producer's rows depend on."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical
from ink_knowledge.proposals import generate,retarget
from ink_knowledge.proposal_views import ProposalViews
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
# A record carrier makes the early-exit producer's supporting law nominal, so
# its identity changes when its definition context is bound.
SOURCE='''module Records;
record Node { id:u32, parent:u32, }
pub fn find(xs:List<Node>,z:Node,k:u32)->Node{return foldr(xs,z,fn(x)=>fn(a)=>choose(x.id==k,x,a));}
'''

class Retarget(unittest.TestCase):
    def test_references_follow_renamed_identities(self):
        value={'dependencies':['old','kept'],'proof':{'Trans':{'right':{'Use':{'law':'old','arguments':{}}},'left':'Normalize'}}}
        out=retarget(value,{'old':'new'})
        self.assertEqual(out['dependencies'],['kept','new'])
        self.assertEqual(out['proof']['Trans']['right']['Use']['law'],'new')
        self.assertIs(retarget(value,{}),value)

    def test_generated_closures_resolve_and_check_with_nominal_carriers(self):
        with tempfile.TemporaryDirectory() as d:
            d=Path(d);source=d/'source.ink';source.write_text(SOURCE);core=d/'core.json';subject=d/'subject.json'
            for args in [['emit-core',source,'-o',core],['emit-semantic',core,'--core','-o',subject]]:
                r=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True)
                self.assertEqual(r.returncode,0,r.stderr)
            store=Store.publish(d/'knowledge',[])
            objects,receipts=generate(json.loads(subject.read_text()),json.loads(core.read_text()))
            early=[r for r in receipts if r.get('module')=='producers.fold_until_laws']
            self.assertTrue(early and early[0]['retargeted']>=1)
            for ident,obj in objects.items():
                for dep in obj['dependencies']:
                    self.assertIn(dep,objects,f'{ident} depends on an object no producer emitted')
            views=ProposalViews(store,objects,d/'views')
            view=d/'view.json';view.write_bytes(canonical(views.bundle(sorted(objects)))+b'\n')
            r=subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True)
            self.assertEqual(r.returncode,0,r.stderr)

if __name__=='__main__':unittest.main()
