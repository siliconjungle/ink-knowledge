"""Batch36 content-bound existing ordered-fold deployments, source binding and full-word replay."""
import copy, hashlib, json, os, random, subprocess, sys, unittest
from pathlib import Path
B = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(B / 'knowledge'), str(B / 'planner')]
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.semantic_laws import value, var, word, term, law, lam, binary, bound
from producers.web_pipeline36_laws import named_laws, reference_laws, source_functions, specialize, publish, law_roles
from producers.web_pipeline32_laws import apply
from tests.test_web_pipeline32_laws import alpha, wrap, frames
C = B / 'reports/web-stack-proofs-32-2026-10-11/main-integration/ink-main-publish'
R = Path(os.environ.get('INK_PIPELINE36_PROOFS_DIR', str(B / 'reports/web-stack-proofs-36-2026-10-11/proofs')))
PRIOR_SNAPSHOT = B / 'knowledge/store/snapshots/b7d979fd4861a1b82897f142737e9b8161f8c2946e9f7fa6514b50aefd45240b.json'


def oracle(name,args,staged):
    xs,ys,seed,k=args;w=lambda x:x & 0xffffffff
    left=lambda x:w((x//k if k else 0)+seed)
    right=lambda x:w((x%k if k else 0)+k)
    post=lambda x:w(x+k if x<seed else x-k)
    accepted=lambda x:(x%k if k else 0)<seed
    step=lambda x,a:w(x+w(a*k) if a<seed else x-a)
    if staged:
        inputs=[x for x in xs if accepted(x)] if '_filtered_' in name else xs
        seq=[left(x) for x in inputs]
        if '_nested_' in name:seq=[post(x) for x in seq]
        if '_concat_' in name:seq += [right(y) for y in ys]
        acc=seed
        for x in reversed(seq):acc=step(x,acc)
        return acc
    acc=seed
    if '_concat_' in name:
        for y in reversed(ys):acc=step(right(y),acc)
    for x in reversed(xs):
        if '_filtered_' in name and not accepted(x):continue
        x=left(x)
        if '_nested_' in name:x=post(x)
        acc=step(x,acc)
    return acc


class Pipeline36(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        R.mkdir(parents=True, exist_ok=True)
        assert hashlib.sha256(C.read_bytes()).hexdigest() == '04f42856696cbc9a4d5b0523e4a2c5d9d84ae28e0e039f0fd9c305fe2d0a5536'
        cls.commands, cls.units, fresh, shared = [], [], [], []
        dummy = B / 'reports/web-stack-proofs-32-2026-10-11/proofs/dummy.core.json'
        (R / 'dummy.core.json').write_bytes(dummy.read_bytes())
        for held in (False, True):
            for name, t, source in source_functions(held):
                d = R / 'checks' / name
                d.mkdir(parents=True, exist_ok=True)
                src, core, sem = d / 'source.ink', d / 'input.core.json', d / 'subject.json'
                src.write_text('module Pipeline36;\n' + source + '\n')
                cls.run_(C, 'emit-core', src, '-o', core)
                cls.run_(C, 'emit-semantic', core, '--core', '-o', sem)
                cp, subject = json.loads(core.read_text()), json.loads(sem.read_text())
                rows, controls = specialize(subject, cp), []
                assert len(rows) == 1 and len(controls) == 0, (name, len(rows), len(controls))
                fresh += rows
                shared += controls
                cls.units.append(dict(name=name, type=t, folder=d, core=core, subject=subject, row=rows[0], shared=controls[0] if controls else None))
        cls.store = publish(R / 'validated-store', fresh + shared)
        cls.run_(C, 'knowledge-check', R / 'dummy.core.json', cls.store.root / 'view.json')
        prior = Store(B/'knowledge', snapshot=PRIOR_SNAPSHOT)
        assert all(identity(semantic_entry(v)) in prior.members() for _,v in reference_laws())
        assert all(identity(semantic_entry(v)) in prior.members() for _,v in shared)
        candidate = [dict(name=n,law=v,id=identity(semantic_entry(v)),role=law_roles().get(n,'source_deployment_certificate')) for n,v in named_laws()+fresh]
        (R.parent/'candidate-rows.json').write_text(json.dumps(candidate,indent=2)+'\n')
        (R / 'source-witnesses.json').write_text(json.dumps([dict(name=n, law=v, id=identity(semantic_entry(v)), role='source_deployment_certificate') for n, v in fresh], indent=2) + '\n')
        (R / 'shared-source-witnesses.json').write_text(json.dumps([dict(name=n, law=v, id=identity(semantic_entry(v)), role='shared_existing_scan_certificate') for n, v in shared], indent=2) + '\n')

    @classmethod
    def run_(cls, *args):
        p = subprocess.run(list(map(str, args)), capture_output=True, text=True)
        cls.commands.append(dict(argv=list(map(str, args)), exit_code=p.returncode, stdout=p.stdout, stderr=p.stderr))
        (R / 'test-commands.json').write_text(json.dumps(cls.commands, indent=2) + '\n')
        assert not p.returncode, p.stderr
        try:
            return json.loads(p.stdout)
        except json.JSONDecodeError:
            return p.stdout

    def test_complete_source_replay(self):
        records = []
        for u in self.units:
            name, d, core = u['name'], u['folder'], u['core']
            _, l = u['row']
            oid = identity(semantic_entry(l))
            pkg = dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=u['subject']['input_core_sha256'], knowledge=self.store.bundle([oid]), applications=[dict(function=name, path=[], law=oid, arguments={n:var(s,n) for n,s in l['params'].items()}, premises=[])])
            sel, selected = d / 'selection.json', d / 'selected.core.json'
            sel.write_bytes(canonical(pkg) + b'\n')
            receipt = self.run_(C, 'check-selection', core, sel)
            (d / 'replay.json').write_text(json.dumps(receipt, indent=2) + '\n')
            self.run_(C, 'emit-core', core, '--core', '--selection', sel, '-o', selected)
            for stage in ('method:map','method:filter','method:concat'):
                self.assertNotIn(stage,canonical(l['to']).decode())
            self.assertIn('call:reduce_word', canonical(l['to']).decode())
            for helper in ('left_word','right_word','post_word','accepts_word'):
                if 'call:'+helper in canonical(l['from']).decode():
                    self.assertIn('call:'+helper,canonical(l['to']).decode())
            rng = random.Random(3303)
            replay_frames = frames('u32') + [([rng.getrandbits(32) for _ in range(nx)], [rng.getrandbits(32) for _ in range(ny)], 0xffffffff, 0) for nx, ny in [(128,1),(1,128),(128,97),(97,128)]]
            for i, args in enumerate(replay_frames):
                f = d / f'args-{i}.json'
                f.write_text(json.dumps(args) + '\n')
                before = self.run_(C, 'run', core, name, f, '--core')
                after = self.run_(C, 'run', selected, name, f, '--core')
                self.assertEqual(before, after)
                self.assertEqual(before, oracle(name, args, True))
                self.assertEqual(before, oracle(name, args, False))
                self.assertIsInstance(before,int)
                records.append(dict(name=name, frame=i, lengths=[len(args[0]),len(args[1])], equal=True))
        (R / 'interpreter.json').write_text(json.dumps(dict(status='passed', typed_sources=4, frames=len(records), records=records), indent=2) + '\n')

    def test_only_new_bound_deployments(self):
        prior=Store(B/'knowledge',snapshot=PRIOR_SNAPSHOT);self.assertEqual(len(prior.members()),2508)
        refs={identity(semantic_entry(v)) for _,v in reference_laws()}
        self.assertTrue(refs <= set(prior.members()));self.assertEqual(named_laws(),[])
        new={identity(semantic_entry(u['row'][1])) for u in self.units}
        self.assertFalse(new & set(prior.members()))
        self.assertEqual(set(self.store.members())-set(prior.members()),new)
        (R/'deployment-novelty.json').write_text(json.dumps(dict(status='passed',prior_entries=2508,prior_snapshot=prior.snapshot_id,new_generic_theorems=0,new_definition_bound_deployments=4,reused_typed_generic_roots=9,new_ids=sorted(new)),indent=2)+'\n')

    def test_reused_typed_ordered_laws_closed(self):
        from producers.semantic_laws import op
        from ink_planner.semantic_search import substitute
        checks=[]
        for name,endpoint in reference_laws():
            t=name.rsplit('_',1)[1];bits=64 if t=='u64' else 32;mask=(1<<bits)-1
            s,ls=value(t.upper()),value({'List':t.upper()})
            def lit(xs):
                out=term(ls,'Nil')
                for x in reversed(xs):out=term(ls,{'Cons':[word(t.upper(),x & mask),out]})
                return out
            for xs,ys,a,k in frames(t)[:7]:
                f=lam(s,binary('+',bound(s,0),word(t.upper(),k & mask)))
                g=lam(s,lam(s,binary('-',bound(s,1),binary('*',bound(s,0),word(t.upper(),3)))))
                predicate=lam(s,op(value('Bool'),'binary:<',bound(s,0),word(t.upper(),a & mask)))
                args=dict(xs=lit(xs),z=word(t.upper(),a & mask),g=g)
                if 'concat_ordered' in name:
                    args['ys']=lit(ys);seq=xs+ys
                else:
                    args['f']=f
                    if 'filtered_mapped' in name:args['p']=predicate;seq=[x for x in xs if x<a]
                    else:seq=xs
                    seq=[wrap(x+k,t) for x in seq]
                acc=a
                for x in reversed(seq):acc=wrap(x-wrap(acc*3,t),t)
                expected=word(t.upper(),acc & mask)
                ends=[substitute(endpoint[key],args) for key in ('from','to')]
                objects=[semantic_entry(law({},v,expected)) for v in ends]
                d=R/'typed-old-law-checks'/f'{name}-{len(checks)}';st=Store.publish(d,objects);view=d/'view.json'
                view.write_bytes(canonical(st.bundle([identity(o) for o in objects]))+b'\n')
                self.run_(C,'knowledge-check',R/'dummy.core.json',view)
                checks.append(dict(law=name,type=t,lengths=[len(xs),len(ys)],initial=a,callback='x-(acc*3)'))
        (R/'typed-old-law-checks.json').write_text(json.dumps(dict(status='passed',checks=checks),indent=2)+'\n')

    def test_rehashed_false_order_default_and_result(self):
        from producers.semantic_laws import op
        from producers.web_sequence_laws import named_laws as sequence
        old=dict(sequence())['concat_ordered_fold_u32'];s,ls=value('U32'),value({'List':'U32'})
        xs,ys,z,g=var(ls,'xs'),var(ls,'ys'),var(s,'z'),var(old['params']['g'],'g')
        wrong_order=copy.deepcopy(old);wrong_order['to']=op(s,'call:foldr',ys,op(s,'call:foldr',xs,z,g),g)
        u=next(x for x in self.units if x['name']=='pipeline36_plain_ordered_u32');original=u['row'][1]
        wrong_default=copy.deepcopy(original);wrong_default['to']['node']['Op'][1][1]=word('U32',0)
        wrong_result=copy.deepcopy(original);wrong_result['to']=word('U32',0)
        controls=[]
        for label,bad in [('wrong_fold_order',wrong_order),('wrong_empty_default',wrong_default),('wrong_result',wrong_result)]:
            obj=semantic_entry(bad);oid=identity(obj);objects={oid:obj}
            def add(i):
                if i not in objects:objects[i]=self.store.object(i)
                for dep in objects[i]['dependencies']:
                    if dep not in objects:add(dep)
            for i in obj['dependencies']:add(i)
            st=Store.publish(R/'false'/label,objects.values());view=st.root/'view.json';view.write_bytes(canonical(st.bundle([oid]))+b'\n')
            p=subprocess.run([str(C),'knowledge-check',str(R/'dummy.core.json'),str(view)],capture_output=True,text=True);self.assertNotEqual(p.returncode,0)
            controls.append(dict(label=label,id=oid,content_hash_valid=True,exit_code=p.returncode,stderr=p.stderr))
        # This concrete noncommutative fold distinguishes forward/reverse order.
        seq=[1,2,7];acc=5
        for x in reversed(seq):acc=(x-acc*3)&0xffffffff
        reverse=acc;acc=5
        for x in seq:acc=(x-acc*3)&0xffffffff
        self.assertNotEqual(reverse,acc)
        (R/'false-theorem-controls.json').write_text(json.dumps(dict(status='rejected',records=controls,order_witness=dict(sequence=seq,initial=5,reverse=reverse,forward=acc)),indent=2)+'\n')

    def test_direct_and_transitive_helper_context_mutations(self):
        records=[]
        for u in self.units:
            _,l=u['row'];oid=identity(semantic_entry(l))
            packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=u['subject']['input_core_sha256'],knowledge=self.store.bundle([oid]),applications=[dict(function=u['name'],path=[],law=oid,arguments={n:var(s,n) for n,s in l['params'].items()},premises=[])])
            context=l['definition_context']['definitions']
            for helper in sorted(context):
                cp=json.loads(u['core'].read_text());f=next(f for f in cp['program']['functions'] if f['name']==helper)
                f['body']={'Bool':False} if f['result']=='Bool' else {'Num':3}
                changed,sem=u['folder']/(helper+'-changed.core.json'),u['folder']/(helper+'-changed.subject.json')
                changed.write_bytes(canonical(cp)+b'\n');self.run_(C,'emit-semantic',changed,'--core','-o',sem)
                fresh=copy.deepcopy(packet);fresh['input_core_sha256']=json.loads(sem.read_text())['input_core_sha256']
                selection=u['folder']/(helper+'-changed.selection.json');selection.write_bytes(canonical(fresh)+b'\n')
                p=subprocess.run([str(C),'check-selection',str(changed),str(selection)],capture_output=True,text=True);self.assertNotEqual(p.returncode,0)
                records.append(dict(name=u['name'],helper=helper,correctly_rehashed_source=True,exit_code=p.returncode,stderr=p.stderr))
        (R/'helper-context-controls.json').write_text(json.dumps(dict(status='rejected',records=records),indent=2)+'\n')

if __name__ == '__main__':
    unittest.main()
