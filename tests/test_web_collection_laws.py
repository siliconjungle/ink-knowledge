"""Real checker, planner replay and hash-valid negative controls."""
import copy,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.web_collection_laws import named_laws,publish
ROOT=Path(__file__).resolve().parents[1]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT.parent/'target/release/ink'))


def benchmark_source():
    out=['module WebCollections;']
    triples=[('u32','bool'),('i32','bool'),('u64','bool'),('f32','bool'),('bool','u32'),('u32','u64'),('u64','u32'),('i32','u32')]
    for a,b in triples:
        name=f'cross_{a}_{b}'
        body='x<0.0' if a=='f32' else 'x<7' if b=='bool' else 'choose(x,1,3)' if a=='bool' else '7'
        reverse='choose(x,1.5,2.5)' if a=='f32' else 'choose(x,11,29)' if b=='bool' else 'x<2' if a=='bool' else '3'
        out.extend([f'fn {name}_first(x:{a})->{b}{{return {body};}}',f'fn {name}_second(x:{b})->{a}{{return {reverse};}}',f'fn {name}(xs:List<{a}>)->List<{a}>{{return xs.map(fn(x)=>{name}_first(x)).map(fn(x)=>{name}_second(x));}}'])
    for t in ('u32','i32','u64','f32','bool'):
        expr='x&&y' if t=='bool' else 'x+y'
        out.append(f'fn zip_{t}(xs:List<{t}>)->List<{t}>{{return xs.zip(xs,fn(x)=>fn(y)=>{expr});}}')
        if t!='bool':
            expr='x*1.5' if t=='f32' else 'x*3';zero='0.0' if t=='f32' else '0'
            out.append(f'fn fold_{t}(xs:List<{t}>)->{t}{{return foldr(xs.map(fn(x)=>{expr}),{zero},fn(x)=>fn(a)=>x-a);}}')
        if t not in ('bool','f32'):
            out.append(f'fn scan_{t}(xs:List<{t}>)->List<{t}>{{return xs.map(fn(x)=>x-x).scan();}}')
    return ('\n'.join(out)+'\n').replace(':bool',':Bool').replace('->bool','->Bool').replace('<bool>','<Bool>')
SOURCE=benchmark_source()


class WebCollectionLawTests(unittest.TestCase):
    def test_deterministic_new_objects(self):
        objects=[semantic_entry(l) for _,l in named_laws()];ids=[identity(o) for o in objects]
        self.assertEqual(len(ids),20);self.assertEqual(len(ids),len(set(ids)))
        self.assertEqual(ids,[identity(semantic_entry(l)) for _,l in named_laws()])
        catalogue=ROOT/'store/objects'
        # Publication legitimately adds these objects to the current store. Compare
        # with the preserved prior catalogue, never mutable current membership.
        prior=Store(ROOT,ROOT/'store/snapshots/3ba66adca49bc68eee035c2addecf55cea8a9533d25741dc9d48f5d24a213be1.json')
        previous_ids=set(prior.members());self.assertFalse(set(ids)&previous_ids)
        statements={(canonical(o['payload']['from']),canonical(o['payload']['to'])) for o in objects}
        for previous_id in previous_ids:
            old=json.loads((catalogue/f'{previous_id}.json').read_text())
            if old.get('kind')=='rewrite':
                p=old['payload'];self.assertNotIn((canonical(p['from']),canonical(p['to'])),statements)

    @unittest.skipUnless(COMPILER.is_file(),'build target/release/ink or set INK_COMPILER')
    def test_checker_and_all_twenty_planner_applications(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);store,manifest=publish(root/'store');source,core,selected=root/'input.ink',root/'core.json',root/'selection.json';source.write_text(SOURCE)
            subprocess.run([COMPILER,'emit-core',source,'-o',core],check=True,capture_output=True)
            checked=subprocess.run([COMPILER,'knowledge-check',core,store.root/'view.json'],check=True,capture_output=True,text=True)
            self.assertEqual(len(json.loads(checked.stdout)['entries']),20)
            # The planner has 12 search rounds. Two ten-stage programs test every
            # executable application without treating that bounded search as a proof.
            lines=SOURCE.splitlines();helpers=[l for l in lines[1:] if '_first(' in l.split('return')[0] or '_second(' in l.split('return')[0]]
            targets=[l for l in lines[1:] if l not in helpers];applied=set()
            for group in (targets[:10],targets[10:]):
                source.write_text('module WebCollections;\n'+'\n'.join(helpers+group)+'\n')
                subprocess.run([COMPILER,'emit-core',source,'-o',core],check=True,capture_output=True)
                subprocess.run([sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',core,'--snapshot',store.data/'snapshot.json','--budget','4096','-o',selected],check=True,capture_output=True)
                package=json.loads(selected.read_text());applied.update(a['law'] for a in package['applications'])
                subprocess.run([COMPILER,'check-selection',core,selected],check=True,capture_output=True)
            self.assertEqual(set(manifest['names'].values())-applied,set())

    @unittest.skipUnless(COMPILER.is_file(),'build target/release/ink or set INK_COMPILER')
    def test_hash_valid_false_zip_and_reversed_fold_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);source,core=root/'input.ink',root/'core.json';source.write_text(SOURCE)
            subprocess.run([COMPILER,'emit-core',source,'-o',core],check=True,capture_output=True)
            laws=dict(named_laws());wrong_zip=copy.deepcopy(laws['self_zip_map_u32'])
            body=wrong_zip['to']['node']['Op'][1][1]['node']['Lambda'];body['node']['Op'][1][1]={'sort':{'Value':'U32'},'node':{'Word':0}}
            wrong_fold=copy.deepcopy(laws['map_ordered_fold_f32']);body=wrong_fold['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']
            body['node']['Op'][1].reverse()
            for name,candidate in [('wrong-zip',wrong_zip),('reversed-fold',wrong_fold)]:
                obj=semantic_entry(candidate);store=Store.publish(root/name,[obj]);view=store.root/'view.json';view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
                rejected=subprocess.run([COMPILER,'knowledge-check',core,view],capture_output=True,text=True)
                self.assertNotEqual(rejected.returncode,0);self.assertIn('semantic normal forms differ',rejected.stderr);self.assertNotIn('identity mismatch',rejected.stderr)

if __name__=='__main__':unittest.main()
