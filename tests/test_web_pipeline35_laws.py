"""Batch35 direct observed mapped-zip fusion, source binding and full-word replay."""
import copy, hashlib, json, os, random, subprocess, sys, unittest
from pathlib import Path
B = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(B / 'knowledge'), str(B / 'planner')]
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.semantic_laws import value, var, word, term, law, lam, binary, bound
from producers.web_pipeline35_laws import named_laws, reference_laws, source_functions, specialize, publish, law_roles
from producers.web_pipeline32_laws import apply
from tests.test_web_pipeline32_laws import alpha, wrap, frames
C = B / 'reports/web-stack-proofs-32-2026-10-11/main-integration/ink-main-publish'
R = Path(os.environ.get('INK_PIPELINE35_PROOFS_DIR', str(B / 'reports/web-stack-proofs-35-2026-10-11/proofs')))
PRIOR_SNAPSHOT = B / 'knowledge/store/snapshots/7cf9b7ec48a8edd25b05951b8e424ea26444467fc176257aa34ac5a8e40aa644.json'


def oracle(name,args,staged):
    xs,ys,seed,k=args
    wrap32=lambda x:x & 0xffffffff
    left=lambda x:wrap32(wrap32((x//k if k else 0)+x)+seed)
    right=lambda y:wrap32(wrap32((y%k if k else 0)+y)+k)
    post=lambda x:wrap32(x+k if x<seed else x-k)
    def combine(a,b):
        if 'heldout' in name:
            return wrap32(wrap32(a+b)*k if a<seed else wrap32(a-b)+seed)
        return wrap32((a+wrap32(b*k) if a<b else a-wrap32(b*k))+seed)
    lm='_left_' in name or '_both_' in name or '_nested_' in name
    rm='_right_' in name or '_both_' in name or '_nested_' in name
    if staged:
        xx=[left(x) for x in xs] if lm else list(xs)
        if '_nested_' in name:xx=[post(x) for x in xx]
        yy=[right(y) for y in ys] if rm else list(ys)
        return [combine(a,b) for a,b in zip(xx,yy)]
    out=[]
    for x,y in zip(xs,ys):
        a,b=left(x) if lm else x,right(y) if rm else y
        if '_nested_' in name:a=post(a)
        out.append(combine(a,b))
    return out


class Pipeline35(unittest.TestCase):
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
                src.write_text('module Pipeline35;\n' + source + '\n')
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
        candidate = [dict(name=n,law=v,id=identity(semantic_entry(v)),role=law_roles().get(n,'definition_bound_source_certificate')) for n,v in named_laws()+fresh]
        (R.parent/'candidate-rows.json').write_text(json.dumps(candidate,indent=2)+'\n')
        (R / 'source-witnesses.json').write_text(json.dumps([dict(name=n, law=v, id=identity(semantic_entry(v)), role='definition_bound_source_certificate') for n, v in fresh], indent=2) + '\n')
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
            self.assertNotIn('method:scan', canonical(l['to']).decode())
            self.assertNotIn('method:map', canonical(l['to']).decode())
            self.assertIn('call:combine_words', canonical(l['to']).decode())
            for helper in ('left_word','right_word','post_word'):
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
                self.assertEqual(len(before), min(len(args[0]), len(args[1])))
                records.append(dict(name=name, frame=i, lengths=[len(args[0]),len(args[1])], equal=True))
        (R / 'interpreter.json').write_text(json.dumps(dict(status='passed', typed_sources=4, frames=len(records), records=records), indent=2) + '\n')

    def test_novelty_current_full_catalogue(self):
        st = Store(B / 'knowledge', snapshot=PRIOR_SNAPSHOT)
        members = st.members()
        self.assertEqual(len(members), 2495)
        new = {alpha(v):n for n,v in named_laws()}
        duplicates, count = [], 0
        for oid in members:
            p = st.object(oid)['payload']
            if not isinstance(p.get('from'),dict) or 'node' not in p['from']:
                continue
            count += 1
            for direction, q in [('forward',p),('reverse',dict(p, **{'from':p['to'],'to':p['from']}))]:
                if alpha(q) in new:
                    duplicates.append(dict(candidate=new[alpha(q)], prior_id=oid, direction=direction))
        self.assertFalse(duplicates)
        self.assertFalse({identity(semantic_entry(v)) for _,v in named_laws()} & set(members))
        (R / 'novelty.json').write_text(json.dumps(dict(status='passed', prior_entries=len(members), prior_snapshot=st.snapshot_id, prior_semantic_pairs=count, duplicates=duplicates, mechanisms=0, derived_endpoints=9, prior_proof_dependencies=21, roles=law_roles()), indent=2) + '\n')

    def test_all_typed_arbitrary_observed_callbacks(self):
        from ink_planner.semantic_search import substitute
        roots=dict(named_laws());checks=[]
        for t in ('u32','i32','u64'):
            bits=64 if t=='u64' else 32;mask=(1<<bits)-1
            s,ls=value(t.upper()),value({'List':t.upper()})
            def lit(xs):
                out=term(ls,'Nil')
                for x in reversed(xs):out=term(ls,{'Cons':[word(t.upper(),x & mask),out]})
                return out
            for family in ('left','right','both'):
                endpoint=roots['independent_'+family+'_observed_mapped_zip_fusion_'+t]
                for xs,ys,a,k in frames(t)[:7]:
                    f=lam(s,binary('+',binary('*',bound(s,0),word(t.upper(),k & mask)),word(t.upper(),a & mask)))
                    r=lam(s,binary('-',bound(s,0),word(t.upper(),a & mask)))
                    h=lam(s,lam(s,binary('-',bound(s,1),binary('*',bound(s,0),word(t.upper(),3)))))
                    args=dict(xs=lit(xs),ys=lit(ys),h=h)
                    if family in ('left','both'):args['f']=f
                    if family in ('right','both'):args['r']=r
                    ends=[substitute(endpoint[key],args) for key in ('from','to')]
                    expected=[]
                    for x,y in zip(xs,ys):
                        if family in ('left','both'):x=wrap(wrap(x*k,t)+a,t)
                        if family in ('right','both'):y=wrap(y-a,t)
                        expected.append(wrap(x-wrap(y*3,t),t))
                    objects=[semantic_entry(law({},v,lit(expected))) for v in ends]
                    d=R/'typed-map-checks'/f'{t}-{family}-{len(checks)}';st=Store.publish(d,objects);view=d/'view.json'
                    view.write_bytes(canonical(st.bundle([identity(o) for o in objects]))+b'\n')
                    self.run_(C,'knowledge-check',R/'dummy.core.json',view)
                    checks.append(dict(type=t,family=family,lengths=[len(xs),len(ys)],seed=a,multiplier=k,callback='x-(y*3)'))
        (R/'typed-map-checks.json').write_text(json.dumps(dict(status='passed',checks=checks),indent=2)+'\n')

    def test_observed_values_cannot_use_old_projection_erasure(self):
        from producers.web_pipeline34_laws import specialize as old_projection
        records=[]
        for u in self.units:
            self.assertEqual(old_projection(u['subject'],json.loads(u['core'].read_text())),[])
            records.append(dict(name=u['name'],old_projection_specializations=0,new_fusion_specializations=1))
        (R/'observed-input-controls.json').write_text(json.dumps(dict(status='passed',records=records),indent=2)+'\n')

    def test_rehashed_false_theorems(self):
        from producers.semantic_laws import op
        s,ls=value('U32'),value({'List':'U32'});un=dict(Arrow=[s,s]);bi=dict(Arrow=[s,un])
        xs,ys,f,h=var(ls,'xs'),var(ls,'ys'),var(un,'f'),var(bi,'h')
        roots=dict(named_laws());controls=[]
        from producers.web_pipeline32_laws import apply
        targets={
            'missing_observed_mapper':op(ls,'method:zip',xs,ys,h),
            'wrong_truncation':op(ls,'method:map',xs,lam(s,apply(apply(h,apply(f,bound(s,0))),word('U32',0)))),
            'reversed_pair_order':op(ls,'method:zip',xs,ys,lam(s,lam(s,apply(apply(h,bound(s,0)),apply(f,bound(s,1))))))}
        for label,target in targets.items():
            bad=copy.deepcopy(roots['independent_left_observed_mapped_zip_fusion_u32']);bad['to']=target
            obj=semantic_entry(bad);oid=identity(obj);objects={oid:obj}
            def add(i):
                if i not in objects:objects[i]=self.store.object(i)
                for dependency in objects[i]['dependencies']:
                    if dependency not in objects:add(dependency)
            for i in obj['dependencies']:add(i)
            st=Store.publish(R/'false'/label,objects.values());view=st.root/'view.json'
            view.write_bytes(canonical(st.bundle([oid]))+b'\n')
            p=subprocess.run([str(C),'knowledge-check',str(R/'dummy.core.json'),str(view)],capture_output=True,text=True)
            self.assertNotEqual(p.returncode,0)
            controls.append(dict(label=label,id=oid,content_hash_valid=True,exit_code=p.returncode,stderr=p.stderr))
        (R/'false-theorem-controls.json').write_text(json.dumps(dict(status='rejected',records=controls),indent=2)+'\n')

    def test_direct_and_transitive_helper_context_mutations(self):
        u=next(x for x in self.units if x['name']=='pipeline35_nested_observed_heldout_u32')
        _,l=u['row'];oid=identity(semantic_entry(l))
        original=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=u['subject']['input_core_sha256'],knowledge=self.store.bundle([oid]),applications=[dict(function=u['name'],path=[],law=oid,arguments={n:var(s,n) for n,s in l['params'].items()},premises=[])])
        records=[]
        for helper in ('left_word','right_word','combine_words','post_word','normalize_left','normalize_right','mix_words','shift_word'):
            cp=json.loads(u['core'].read_text());next(f for f in cp['program']['functions'] if f['name']==helper)['body']={'Num':3}
            changed,sem=u['folder']/(helper+'-changed.core.json'),u['folder']/(helper+'-changed.subject.json')
            changed.write_bytes(canonical(cp)+b'\n');self.run_(C,'emit-semantic',changed,'--core','-o',sem)
            packet=copy.deepcopy(original);packet['input_core_sha256']=json.loads(sem.read_text())['input_core_sha256']
            selection=u['folder']/(helper+'-changed.selection.json');selection.write_bytes(canonical(packet)+b'\n')
            p=subprocess.run([str(C),'check-selection',str(changed),str(selection)],capture_output=True,text=True)
            self.assertNotEqual(p.returncode,0)
            records.append(dict(helper=helper,correctly_rehashed_source=True,exit_code=p.returncode,stderr=p.stderr))
        (R/'helper-context-controls.json').write_text(json.dumps(dict(status='rejected',records=records),indent=2)+'\n')

if __name__ == '__main__':
    unittest.main()
