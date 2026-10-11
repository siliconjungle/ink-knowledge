"""Batch38 observed padded indexed-map fusion laws, source binding and full-word replay."""
import copy, hashlib, json, os, random, subprocess, sys, unittest
from pathlib import Path
B = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(B / 'knowledge'), str(B / 'planner')]
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.semantic_laws import value, var, word, term, law, lam, binary, bound
from producers.web_pipeline38_laws import named_laws, grouped_laws, source_functions, specialize, publish, law_roles
from producers.web_pipeline32_laws import apply
from tests.test_web_pipeline32_laws import alpha, wrap, frames
C = B / 'reports/web-stack-proofs-32-2026-10-11/main-integration/ink-main-publish'
R = Path(os.environ.get('INK_PIPELINE38_PROOFS_DIR', str(B / 'reports/web-stack-proofs-38-2026-10-11/proofs')))
PRIOR_SNAPSHOT=B/'knowledge/store/snapshots/6df4df9aae82d58eba9eac5e8d36b41ce37147ed5d661285903745f4c136d9e3.json'


def oracle(name,args,staged):
    xs,ys,seed,k=args
    mask=0xffffffff
    def pair(a,b):
        if 'heldout' in name:return ((a//k if k else 0)+b if a<b else (b%k if k else 0)+a)&mask
        return (a+b*k if a<b else a-b+seed)&mask
    left=[];right=[]
    for i,x in enumerate(xs):
        if 'heldout' in name:
            a=((x//k if k else 0)+(i%k if k else 0)+seed)&mask
            b=(x+k if i<seed else x*3)&mask
        else:
            a=(x+k if i<seed else x-seed)&mask
            b=(x*k if i%3==0 else x+seed)&mask
        left.append(a);right.append(b)
    if staged:
        if '_left_' in name:left+=ys
        else:right+=ys
    return [pair(a,b) for a,b in zip(left,right)]


class Pipeline38(unittest.TestCase):
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
                src.write_text('module Pipeline38;\n' + source + '\n')
                cls.run_(C, 'emit-core', src, '-o', core)
                cls.run_(C, 'emit-semantic', core, '--core', '-o', sem)
                cp, subject = json.loads(core.read_text()), json.loads(sem.read_text())
                rows, controls = specialize(subject, cp), []
                assert len(rows) == 1 and len(controls)==0, (name, len(rows), len(controls))
                fresh += rows
                shared += controls
                cls.units.append(dict(name=name, type=t, folder=d, core=core, subject=subject, row=rows[0], shared=controls[0] if controls else None))
        cls.store = publish(R / 'validated-store', fresh + shared)
        cls.run_(C, 'knowledge-check', R / 'dummy.core.json', cls.store.root / 'view.json')
        candidate=[dict(name=n,law=v,id=identity(semantic_entry(v)),role=law_roles().get(n,'definition_bound_source_certificate')) for n,v in named_laws()+fresh]
        (R.parent/'candidate-rows.json').write_text(json.dumps(candidate,indent=2)+'\n')
        (R / 'source-witnesses.json').write_text(json.dumps([dict(name=n, law=v, id=identity(semantic_entry(v)), role='definition_bound_source_certificate') for n, v in fresh], indent=2) + '\n')
        (R / 'shared-source-witnesses.json').write_text(json.dumps([dict(name=n, law=v, id=identity(semantic_entry(v)), role='shared_normalize_only_definition_transport') for n, v in shared], indent=2) + '\n')

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
            self.assertEqual(canonical(l['to']).decode().count('method:map_indexed'),1)
            self.assertNotIn('method:concat',canonical(l['to']).decode())
            self.assertNotIn('method:zip',canonical(l['to']).decode())
            for helper in ('left_word','right_word','pair_word'):self.assertIn('call:'+helper,canonical(l['to']).decode())
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
                self.assertEqual(len(before), len(args[0]))
                records.append(dict(name=name, frame=i, lengths=[len(args[0]),len(args[1])], equal=True))
        (R / 'interpreter.json').write_text(json.dumps(dict(status='passed', typed_sources=4, frames=len(records), records=records), indent=2) + '\n')

    def test_novelty_current_full_catalogue(self):
        st = Store(B / 'knowledge',snapshot=PRIOR_SNAPSHOT)
        members = st.members()
        self.assertEqual(len(members), 2534)
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
        (R / 'novelty.json').write_text(json.dumps(dict(status='passed', prior_entries=len(members), prior_snapshot=st.snapshot_id, prior_semantic_pairs=count, duplicates=duplicates, mechanisms=1, typed_endpoints=6, supports=6, roles=law_roles()), indent=2) + '\n')

    def test_generalized_nat_offsets_and_index_wrap(self):
        from producers.semantic_laws import op,nat
        from ink_planner.semantic_search import substitute
        roots=dict(grouped_laws()[0]);checks=[]
        starts=[0,1,2**32-2,2**32-1,2**32,2**32+1,2**32+17]
        for t in ('u32','i32','u64'):
            bits=64 if t=='u64' else 32;mask=(1<<bits)-1;s,ls=value(t.upper()),value({'List':t.upper()});ix=value('U32')
            f=lam(ix,lam(s,op(s,'call:choose',op(value('Bool'),'binary:<',bound(ix,1),word('U32',3)),binary('+',bound(s,0),word(t.upper(),7)),binary('-',bound(s,0),word(t.upper(),7)))))
            g=lam(ix,lam(s,op(s,'call:choose',op(value('Bool'),'binary:==',op(ix,'call:rem_or',bound(ix,1),word('U32',3),word('U32',0)),word('U32',0)),binary('*',bound(s,0),word(t.upper(),3)),binary('+',bound(s,0),word(t.upper(),2)))))
            h=lam(s,lam(s,binary('-',bound(s,1),bound(s,0))))
            def lit(xs):
                out=term(ls,'Nil')
                for x in reversed(xs):out=term(ls,{'Cons':[word(t.upper(),x & mask),out]})
                return out
            for side in ('left','right'):
                support=roots[side+'_padded_indexed_beta_'+t]
                for frame,(xs,ys,a,_) in enumerate(frames(t)[:7]):
                    v=substitute(support['from'],dict(xs=lit(xs),ys=lit(ys),f=f,g=g,h=h,n=nat(starts[frame])))
                    expected=[]
                    for j,x in enumerate(xs):
                        i=(starts[frame]+j)&0xffffffff;first=wrap(x+7 if i<3 else x-7,t);second=wrap(x*3 if i%3==0 else x+2,t);expected.append(wrap(first-second,t))
                    obj=semantic_entry(law({},v,lit(expected)));d=R/'offset-checks'/f'{t}-{side}-{len(checks)}';st=Store.publish(d,[obj]);view=d/'view.json';view.write_bytes(canonical(st.bundle([identity(obj)]))+b'\n');self.run_(C,'knowledge-check',R/'dummy.core.json',view)
                    checks.append(dict(type=t,side=side,lengths=[len(xs),len(ys)],start_nat=starts[frame],word_index_wrap=starts[frame]>=2**32-2))
        (R/'offset-checks.json').write_text(json.dumps(dict(status='passed',checks=checks),indent=2)+'\n')

    def test_same_origin_appended_suffix_scope(self):
        from producers.semantic_laws import op,arrow
        s,ls=value('U32'),value({'List':'U32'});ix=value('U32');xs,ys=var(ls,'xs'),var(ls,'ys');records=[]
        f=lam(ix,lam(s,binary('+',bound(s,0),word('U32',1))));g=lam(ix,lam(s,binary('*',bound(s,0),word('U32',3))));h=lam(s,lam(s,binary('-',bound(s,1),bound(s,0))))
        for side in ('left','right'):
            for defect in ('different_origin','prepended_suffix'):
                left=op(ls,'method:map_indexed',xs,f);right=op(ls,'method:map_indexed',ys if defect=='different_origin' else xs,g)
                if side=='left':left=op(ls,'method:concat',ys,left) if defect=='prepended_suffix' else op(ls,'method:concat',left,ys)
                else:right=op(ls,'method:concat',ys,right) if defect=='prepended_suffix' else op(ls,'method:concat',right,ys)
                body=op(ls,'method:zip',left,right,h);self.assertEqual(specialize(dict(functions={'observed':body})),[]);records.append(dict(side=side,defect=defect,specializations=0))
        (R/'projection-scope-controls.json').write_text(json.dumps(dict(status='passed',records=records),indent=2)+'\n')

    def test_rehashed_false_extent_offset_and_pair_order(self):
        from producers.semantic_laws import op
        root=grouped_laws()[1][0][1];s,ls=value('U32'),value({'List':'U32'});ix=value('U32')
        bad_extent=copy.deepcopy(root);bad_extent['to']=op(ls,'method:concat',bad_extent['to'],var(ls,'ys'))
        bad_order=copy.deepcopy(root);payload=bad_order['to']['node']['Op'][1][1]['node']['Lambda']['node']['Lambda'];a,b=payload['node']['Op'][1][0]['node']['Op'][1][1],payload['node']['Op'][1][1];payload['node']['Op'][1]=[apply(var(root['params']['h'],'h'),b),a]
        bad_offset=copy.deepcopy(root);fused=bad_offset['to']['node']['Op'][1][1];first=fused['node']['Lambda']['node']['Lambda']['node']['Op'][1][0]['node']['Op'][1][1];first['node']['Op'][1][0]['node']['Op'][1][1]=binary('+',bound(ix,1),word('U32',1))
        records=[]
        for label,bad in [('wrong_suffix_extent',bad_extent),('wrong_pair_order',bad_order),('wrong_index_offset',bad_offset)]:
            obj=semantic_entry(bad);oid=identity(obj);objects={oid:obj}
            def add(i):
                if i not in objects:objects[i]=self.store.object(i)
                for d in objects[i]['dependencies']:
                    if d not in objects:add(d)
            for i in obj['dependencies']:add(i)
            st=Store.publish(R/'false'/label,objects.values());view=st.root/'view.json';view.write_bytes(canonical(st.bundle([oid]))+b'\n');p=subprocess.run([str(C),'knowledge-check',str(R/'dummy.core.json'),str(view)],capture_output=True,text=True);self.assertNotEqual(p.returncode,0);records.append(dict(label=label,id=oid,content_hash_valid=True,exit_code=p.returncode,stderr=p.stderr))
        (R/'false-theorem-controls.json').write_text(json.dumps(dict(status='rejected',records=records),indent=2)+'\n')

    def test_direct_and_transitive_helper_binding(self):
        records=[]
        for u in self.units:
            _,l=u['row'];oid=identity(semantic_entry(l));packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=u['subject']['input_core_sha256'],knowledge=self.store.bundle([oid]),applications=[dict(function=u['name'],path=[],law=oid,arguments={n:var(s,n) for n,s in l['params'].items()},premises=[])])
            for helper in sorted(l['definition_context']['definitions']):
                cp=json.loads(u['core'].read_text());next(f for f in cp['program']['functions'] if f['name']==helper)['body']={'Num':3}
                changed,sem=u['folder']/(helper+'-changed.core.json'),u['folder']/(helper+'-changed.subject.json');changed.write_bytes(canonical(cp)+b'\n');self.run_(C,'emit-semantic',changed,'--core','-o',sem)
                fresh=copy.deepcopy(packet);fresh['input_core_sha256']=json.loads(sem.read_text())['input_core_sha256'];selection=u['folder']/(helper+'-changed.selection.json');selection.write_bytes(canonical(fresh)+b'\n')
                p=subprocess.run([str(C),'check-selection',str(changed),str(selection)],capture_output=True,text=True);self.assertNotEqual(p.returncode,0);records.append(dict(name=u['name'],helper=helper,source_correctly_rehashed=True,exit_code=p.returncode,stderr=p.stderr))
        (R/'helper-binding-controls.json').write_text(json.dumps(dict(status='rejected',records=records),indent=2)+'\n')

if __name__ == '__main__':
    unittest.main()
