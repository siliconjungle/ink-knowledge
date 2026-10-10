"""Generic two-consumer sum identities with same-policy prior/new evidence."""
import copy
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.web_reduction15_laws import named_laws,publish,source_functions
from producers.beta_specialization15 import derive

ROOT=Path(__file__).resolve().parents[1]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
BASELINE=ROOT/'store/snapshots/0510381225f45dc33922b2ead3794abd79c190bc3b3cbc34ce41d50e959ed8b1.json'
COMPILER_SHA='45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08'
MODEL=dict(schema=1,operation_costs={'method:map':12,'method:filter':60,'call:sum':10,'call:foldr':80,'apply':20})


def wrap(t,x):
    bits=64 if t=='u64' else 32
    x &= (1<<bits)-1
    return x-(1<<bits) if t=='i32' and x>=1<<(bits-1) else x


def frames(t):
    bits=64 if t=='u64' else 32
    lo,hi=(-(1<<31),(1<<31)-1) if t=='i32' else (0,(1<<bits)-1)
    values=[([],hi,hi),([lo,0,1,hi],7,7),([hi,lo],hi,-3 if t=='i32' else hi-2),([0,1,hi],0,0),([lo,hi,1],1,1)]
    rng=random.Random(15)
    for n in (17,31):
        values.append(([rng.randint(lo,hi) for _ in range(n)],rng.randint(lo,hi),rng.randint(lo,hi)))
    return values


def stage_and_math(name,xs,seed,k,heldout=False):
    t=name.rsplit('_',1)[1];w=lambda x:wrap(t,x)
    # Source stages wrap every primitive; independent math uses unbounded abs/products.
    mapped_f=[w(x-k) if x>k else w(k-x) for x in xs] if heldout else [w(seed-x) if x<seed else w(x-seed) for x in xs]
    mapped_g=[w(w(x*x)+seed) for x in xs] if heldout else [w(w(x+seed)*k) for x in xs]
    a=b=0
    for x in mapped_f:a=w(a+x)
    for x in mapped_g:b=w(b+x)
    if 'weighted' in name:literal=w(w(a*k)+w(b*seed))
    elif 'subtract' in name:literal=w(a-b)
    else:literal=w(a+b)
    unbounded_f=sum(abs(x-(k if heldout else seed)) for x in xs)
    unbounded_g=sum(x*x+seed if heldout else (x+seed)*k for x in xs)
    if 'weighted' in name:oracle=w(unbounded_f*k+unbounded_g*seed)
    elif 'subtract' in name:oracle=w(unbounded_f-unbounded_g)
    else:oracle=w(unbounded_f+unbounded_g)
    return literal,oracle


class Reduction15Tests(unittest.TestCase):
    def setUp(self):
        self.receipts=[]
        archive=os.environ.get('INK_REDUCTION15_EVIDENCE')
        if archive:
            self.directory=Path(archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
        else:
            self.temporary=tempfile.TemporaryDirectory(prefix='ink-reduction15-');self.directory=Path(self.temporary.name)
    def tearDown(self):
        if os.environ.get('INK_REDUCTION15_EVIDENCE'):(self.directory/'commands.json').write_text(json.dumps(self.receipts,indent=2)+'\n')
        else:self.temporary.cleanup()
    def run_command(self,*args,success=True):
        r=subprocess.run(list(map(str,args)),capture_output=True,text=True)
        self.receipts.append(dict(argv=r.args,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
        if success:self.assertEqual(r.returncode,0,r.stderr)
        return r
    def source(self,functions,label):
        source,core=self.directory/f'{label}.ink',self.directory/f'{label}.core.json'
        source.write_text('module Reduction15;\n'+'\n'.join(text for _,text in functions)+'\n')
        self.run_command(COMPILER,'emit-core',source,'-o',core);return source,core

    def test_nine_fresh_generic_endpoints_against_immutable_1031(self):
        objects=[semantic_entry(l) for _,l in named_laws()];ids=[identity(o) for o in objects]
        self.assertEqual(len(ids),9);self.assertEqual(len(set(ids)),9)
        self.assertEqual(ids,[identity(semantic_entry(l)) for _,l in named_laws()])
        old=Store(ROOT,BASELINE);self.assertEqual(len(old.members()),1031);self.assertFalse(set(ids)&set(old.members()))
        endpoints={(canonical(o['payload']['from']),canonical(o['payload']['to'])) for o in objects}
        for i in old.members():
            o=old.object(i)
            if o['kind']=='rewrite' and 'from' in o['payload']:self.assertNotIn((canonical(o['payload']['from']),canonical(o['payload']['to'])),endpoints)

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
    def test_admit_default_and_aggregate_policy_replay_reify_all_typed_recipes(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),COMPILER_SHA)
        planner=ROOT.parent/'planner/ink_planner/semantic_search.py';planner_before=hashlib.sha256(planner.read_bytes()).hexdigest()
        isolated,manifest=publish(self.directory/'isolated')
        pinned=Store(ROOT,BASELINE)
        prior=Store.publish(self.directory/'prior',[pinned.object(i) for i in sorted(pinned.members())]);prior.rebuild()
        _,all_core=self.source(source_functions(),'admission')
        admitted=json.loads(self.run_command(COMPILER,'knowledge-check',all_core,isolated.root/'view.json').stdout)
        self.assertEqual(set(admitted['entries']),set(manifest['names'].values()))
        specialized=[]
        for heldout in (False,True):
            _,sc=self.source(source_functions(heldout),'specializations-'+str(heldout))
            subject=self.directory/f'subject-{heldout}.json'
            self.run_command(COMPILER,'emit-semantic',sc,'--core','-o',subject)
            specialized += derive(json.loads(subject.read_text()),named_laws())
        objects={identity(semantic_entry(v)):semantic_entry(v) for _,v in specialized}
        self.assertEqual(len(objects),18)
        new=Store.publish(self.directory/'combined',[prior.object(i) for i in sorted(prior.members())]+[isolated.object(i) for i in sorted(isolated.members())]+list(objects.values()));new.rebuild()
        view=self.directory/'specialization-view.json';view.write_bytes(canonical(new.bundle(sorted(objects)))+b'\n')
        self.run_command(COMPILER,'knowledge-check',all_core,view)
        (self.directory/'specializations.json').write_text(json.dumps([dict(name=n,law=v,id=identity(semantic_entry(v))) for n,v in specialized],indent=2)+'\n')
        model=self.directory/'aggregate-model.json';model.write_text(json.dumps(MODEL,indent=2)+'\n')
        rows=[];policies=[]
        for heldout in (False,True):
            functions=source_functions(heldout)
            for index in range(0,len(functions),3):
                group=functions[index:index+3];label=f'{"heldout" if heldout else "discovery"}-{index}';source,core=self.source(group,label)
                for policy in ('default','aggregate'):
                    selections={};bodies={}
                    for kind,store in [('prior',prior),('new',new)]:
                        path=self.directory/f'{label}-{policy}-{kind}.selection.json'
                        extra=['--cost-model',model] if policy=='aggregate' else []
                        self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',core,'--knowledge-root',store.root,'--snapshot',store.data/'snapshot.json','--budget',4096,*extra,'-o',path)
                        selections[kind]=json.loads(path.read_text());self.run_command(COMPILER,'check-selection',core,path)
                        selected=self.directory/f'{label}-{policy}-{kind}.selected.core.json';self.run_command(COMPILER,'emit-core',source,'--selection',path,'-o',selected)
                        bodies[kind]={f['name']:f['body'] for f in json.loads(selected.read_text())['program']['functions']}
                    policies.append(dict(source=label,policy=policy,prior_applications=selections['prior']['applications'],new_applications=selections['new']['applications']))
                    if policy=='default':continue
                    for name,_ in group:
                        selected_ids={a['law'] for a in selections['new']['applications'] if a['function']==name}
                        self.assertTrue(any(i in objects and manifest['names'][name] in objects[i]['dependencies'] for i in selected_ids))
                        self.assertNotEqual(bodies['new'][name],bodies['prior'][name])
                        self.assertEqual(bodies['new'][name]['Call'][0],'sum')
                        t=name.rsplit('_',1)[1]
                        path=self.directory/f'{label}-{policy}-new.selection.json'
                        for fi,(xs,seed,k) in enumerate(frames(t)):
                            args=[xs,seed,k];literal,oracle=stage_and_math(name,xs,seed,k,heldout)
                            self.assertEqual(literal,oracle)
                            ap=self.directory/f'{label}-{name}-{fi}.args.json';ap.write_text(json.dumps(args)+'\n')
                            actual=json.loads(self.run_command(COMPILER,'run',source,name,ap).stdout)
                            changed=json.loads(self.run_command(COMPILER,'run',source,name,ap,'--selection',path).stdout)
                            self.assertEqual(actual,oracle);self.assertEqual(changed,oracle)
                            rows.append(dict(function=name,heldout=heldout,args=args,original=actual,selected=changed,oracle=oracle))
        self.assertEqual(len(rows),126)
        (self.directory/'interpreter-results.json').write_text(json.dumps(rows,indent=2)+'\n')
        (self.directory/'policy-comparison.json').write_text(json.dumps(policies,indent=2)+'\n')
        self.assertEqual(hashlib.sha256(planner.read_bytes()).hexdigest(),planner_before)
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),COMPILER_SHA)

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
    def test_three_hash_valid_false_consumer_weights_rejected_semantically(self):
        _,core=self.source(source_functions(),'negative')
        named=dict(named_laws());cases=[]
        for family in ('dual_sum_add','dual_sum_subtract','dual_sum_weighted'):
            candidate=copy.deepcopy(named[family+'_u32'])
            combined = candidate['to']['node']['Op'][1][0]['node']['Op'][1][1]['node']['Lambda']
            if family == 'dual_sum_add':
                combined['node']['Op'][0] = 'binary:-'
            elif family == 'dual_sum_subtract':
                combined['node']['Op'][0] = 'binary:+'
            else:
                a, b = combined['node']['Op'][1]
                a['node']['Op'][1][1], b['node']['Op'][1][1] = b['node']['Op'][1][1], a['node']['Op'][1][1]
            cases.append((family,candidate))
        for family,candidate in cases:
            obj=semantic_entry(candidate);store=Store.publish(self.directory/family,[obj]);view=store.root/'view.json';view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
            r=self.run_command(COMPILER,'knowledge-check',core,view,success=False)
            self.assertNotEqual(r.returncode,0);self.assertIn('semantic normal forms differ',r.stderr);self.assertNotIn('identity mismatch',r.stderr)

if __name__=='__main__':unittest.main()
