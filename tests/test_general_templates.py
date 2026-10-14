"""Indexed templates reference checked generic laws without algorithm matchers."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.store import entry
from ink_knowledge.law_templates import from_general,generate

ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))

class GeneralTemplates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory();cls.directory=Path(cls.temporary.name)
        d=cls.directory
        def run(*args):
            result=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True,timeout=120)
            if result.returncode:raise AssertionError(result.stderr)
            return result
        receipt=json.loads(run('emit-laws',ROOT/'knowledge/libraries/independent-fold-batching.ink','-o',d/'bundle.json').stdout)
        cls.bundle=json.loads((d/'bundle.json').read_text());cls.rule=receipt['names']['independent_fold_batch']
        source=ROOT/'knowledge/libraries/examples/independent-fold-batching.ink'
        run('emit-core',source,'-o',d/'core.json')
        run('emit-semantic',d/'core.json','--core','-o',d/'subject.json')
        cls.core=json.loads((d/'core.json').read_text());cls.subject=json.loads((d/'subject.json').read_text())
    @classmethod
    def tearDownClass(cls):cls.temporary.cleanup()
    def store(self,label,objects=None):
        return Store.publish(self.directory/label,self.bundle['objects'].values()if objects is None else objects)
    def check(self,store,root,accepted=True):
        path=store.root/'view.json';path.write_bytes(canonical(store.bundle([root])))
        result=subprocess.run([str(COMPILER),'knowledge-check',str(self.directory/'core.json'),str(path)],capture_output=True,text=True,timeout=120)
        self.assertEqual(result.returncode==0,accepted,result.stderr)
    def test_words_float_order_and_record_lanes_are_discovered_and_proved(self):
        store=self.store('valid');template=from_general(store,self.rule);store=store.extend([template])
        objects,receipts=generate(store,self.subject,self.core)
        store=store.extend(objects.values());found={}
        for name,body in self.subject['functions'].items():
            for ident,obj in objects.items():
                if obj['payload']['from']==body:
                    self.check(store,ident);found[name]=ident
        self.assertEqual(set(found),{'words','floating','columns'})
        self.assertTrue(receipts)
        # A captured original seed cannot become the evolving accumulator.
        self.assertNotIn('captured_seed',found)
        original=objects[found['words']]
        bad=dict(schema=1,semantics=original['semantics'],dependencies=original['dependencies'],**copy.deepcopy(original['payload']))
        bad['to']['node']['Op'][1][0]['node']='Nil'
        forged=semantic_entry(bad);store=store.extend([forged])
        self.check(store,identity(forged),accepted=False)
    def test_fixed_dependencies_require_snapshot_membership_and_law_role(self):
        store=self.store('dependencies');template=from_general(store,self.rule)
        # Even removing the declared entry dependency cannot bypass the pinned
        # dependency lookup in template acquisition.
        bad=copy.deepcopy(template);bad['dependencies']=[]
        missing=self.store('missing',[bad])
        with self.assertRaises(ValueError):generate(missing,self.subject,self.core)
        definition=entry('definition','not-a-law',{})
        bad['payload']['fixed_dependencies']=[identity(definition)]
        wrong=self.store('wrong-role',[bad,definition])
        with self.assertRaisesRegex(ValueError,'dependency role'):generate(wrong,self.subject,self.core)
    def test_factory_does_not_drop_unproved_premises(self):
        store=self.store('premises');original=self.bundle['objects'][self.rule]
        payload=copy.deepcopy(original['payload']);payload['conditions']=[{'from':payload['from'],'to':payload['to']}]
        law=dict(schema=1,semantics=original['semantics'],dependencies=original['dependencies'],**payload)
        conditional=semantic_entry(law);store=store.extend([conditional])
        with self.assertRaisesRegex(ValueError,'no unproved premises'):from_general(store,identity(conditional))
    def test_normal_planner_discovers_and_composes_without_forcing_selection(self):
        store=self.store('normal-planner');store=store.extend([from_general(store,self.rule)])
        directory=self.directory/'normal-discovery';directory.mkdir()
        import sys
        result=subprocess.run([sys.executable,'-m','ink_planner.compiled_planning',
            '--compiler',str(COMPILER),'--source',str(ROOT/'knowledge/libraries/examples/independent-fold-batching.ink'),
            '--knowledge-root',str(store.root),'--target','javascript','--planning-effort','quick',
            '--measurement-mode','off','--cache','off','--time-seconds','60',
            '--keep-candidates',str(directory/'candidates'),'-o',str(directory/'plan.json')],
            cwd=ROOT,capture_output=True,text=True,timeout=120)
        self.assertEqual(result.returncode,0,result.stderr)
        report=json.loads(result.stdout)
        self.assertEqual(report['status'],'checked')
        selected=json.loads((directory/'plan.json').read_text())
        self.assertEqual(selected['steps'],[],report['selection'])
        found=set();composed=False
        for path in (directory/'candidates').glob('*.plan.json'):
            plan=json.loads(path.read_text());uses=False
            for step in plan['steps']:
                if step['kind']!='rewrite':continue
                package=step['package']
                if self.rule in package['knowledge']['objects']:
                    uses=True;found.update(a['function']for a in package['applications'])
            composed|=uses and len(plan['steps'])>1
        self.assertTrue({'words','floating','columns'}<=found,found)
        self.assertNotIn('captured_seed',found)
        self.assertTrue(composed,'ordinary search should compose the proved rewrite')

if __name__=='__main__':unittest.main()
