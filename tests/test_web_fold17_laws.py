"""Small proof closures and batched typed oracle evidence for ordered folds."""
import copy
import hashlib
import json
import math
import os
from pathlib import Path
import random
import struct
import subprocess
import sys
import tempfile
import unittest
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.beta_specialization15 import derive
from producers.web_fold17_laws import named_laws,dependency_objects,publish,source_functions

ROOT=Path(__file__).resolve().parents[1]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT.parent.parent/'toolchain/ink-sequence-proofs')).resolve()
PIN='cc8308b40f651cdc3e5ece5b32ea94cea81bc2596046680384138fa16dd8ed9a'
BASELINE=ROOT/'store/snapshots'/f'{PIN}.json'


def alpha_endpoints(law):
    names={}
    def walk(v):
        if isinstance(v,dict):
            if set(v)=={'Free'}:
                n=v['Free']
                if n not in names:names[n]='v'+str(len(names))
                return {'Free':names[n]}
            return {k:walk(v[k]) for k in sorted(v)}
        if isinstance(v,list):return [walk(x) for x in v]
        return v
    return canonical(walk([law['from'],law['to']]))


def number(v):
    return struct.unpack('<f',struct.pack('<I',v['F32Bits']))[0] if isinstance(v,dict) else v


def normalize(v,t):
    if t=='f32':
        try:return struct.unpack('<f',struct.pack('<f',v))[0]
        except OverflowError:return math.copysign(math.inf,v)
    bits=64 if t=='u64' else 32;v&=(1<<bits)-1
    return v-(1<<32) if t=='i32' and v>=1<<31 else v


def bits_or_word(v,t):
    return struct.unpack('<I',struct.pack('<f',number(v)))[0] if t=='f32' else v


def callbacks(args,t,alternate):
    _,_,seed,k=args;seed,k=number(seed),number(k);n=lambda v:normalize(v,t)
    f=(lambda x:n(seed-x) if x<seed else n(x-seed)) if alternate else (lambda x:n(n(x*3)+k))
    g=(lambda x,a:n(x-a) if a<seed else n(x+a)) if alternate else (lambda x,a:n(x+n(a*k)) if x<seed else n(x-a))
    return f,g,seed


def eager_oracle(name,args,alternate,reverse=True):
    """Literal map allocations and concat order, followed by the ordered fold."""
    t=name.rsplit('_',1)[1];f,g,z=callbacks(args,t,alternate)
    xs,ys=[number(x) for x in args[0]],[number(x) for x in args[1]]
    values=[f(x) for x in xs]
    if name.startswith('mapped_prefix_'):values=values+ys
    elif name.startswith('mapped_concat_'):values=values+[f(y) for y in ys]
    acc=z;true=false=0
    for x in reversed(values) if reverse else values:
        guard=acc<z if alternate else x<z
        true+=int(guard);false+=int(not guard);acc=g(x,acc)
    return acc,dict(reducer_true=true,reducer_false=false,items=len(values))


def streamed_oracle(name,args,alternate):
    """Visit raw suffix then prefix separately; no concatenated/mapped list."""
    t=name.rsplit('_',1)[1];f,g,acc=callbacks(args,t,alternate)
    if name.startswith('mapped_concat_'):
        for y in reversed(args[1]):acc=g(f(number(y)),acc)
    elif name.startswith('mapped_prefix_'):
        for y in reversed(args[1]):acc=g(number(y),acc)
    for x in reversed(args[0]):acc=g(f(number(x)),acc)
    return acc


def frames(t):
    # Independent arrays, both empty directions and unequal lengths. NaN payload
    # matching is checked between actual executions; Python oracle checks class.
    if t=='f32':
        special=[{'F32Bits':0x7fc00000},{'F32Bits':0x7f800000},{'F32Bits':0xff800000},-0.0]
        result=[[[],[],0.25,-2.0],[[0.0,-0.0,1.5,-2.0],[],2.0,1.0],
            [[],[-1.0,3.0,-0.0],2.0,1.0],[[1.0,-2.0],[3.0,0.0,-0.0],2.0,3.0],
            [special,[0.0,1.0,-0.0],2.0,1.0],[[1.0,-0.0],special,2.0,1.0],
            [[0.0,-0.0,1.5,-2.0],[3.0,-4.0],{'F32Bits':0x7fc00000},2.0],
            [[0.0,1.0],[2.0,-0.0],2.0,{'F32Bits':0x7fc00000}],
            [[0.0,-0.0],[1.0,-1.0],-0.0,{'F32Bits':0x7f800000}]]
    else:
        bits=64 if t=='u64' else 32;high=(1<<31)-1 if t=='i32' else (1<<bits)-1
        low=-(1<<31) if t=='i32' else 0
        result=[[[],[],high,high],[[low,high,0,1],[],7,2],[[],[high,1,0],7,2],
                [[1,2],[3,4,5],7,3],[[high,high,1],[low,0,1,high],low,normalize(-1,t)]]
    rng=random.Random(17)
    for nx,ny in [(17,5),(3,31)]:
        if t=='f32':
            xs=[rng.randrange(-256,256)/8 for _ in range(nx)];ys=[rng.randrange(-256,256)/8 for _ in range(ny)]
            result.append([xs,ys,17.0,3.0])
        else:
            bits=64 if t=='u64' else 32
            result.append([[normalize(rng.getrandbits(bits),t) for _ in range(nx)],
                [normalize(rng.getrandbits(bits),t) for _ in range(ny)],
                normalize(rng.getrandbits(bits),t),normalize(rng.getrandbits(bits),t)])
    return result


class Fold17Tests(unittest.TestCase):
    def setUp(self):
        self.commands=[];self.archive=os.environ.get('INK_FOLD17_EVIDENCE')
        if self.archive:self.directory=Path(self.archive).resolve()/self._testMethodName;self.directory.mkdir(parents=True,exist_ok=True)
        else:self.tmp=tempfile.TemporaryDirectory(prefix='ink-fold17-');self.directory=Path(self.tmp.name)

    def tearDown(self):
        if self.archive:(self.directory/'commands.json').write_text(json.dumps(self.commands,indent=2)+'\n')
        else:self.tmp.cleanup()

    def run_command(self,*args,success=True):
        argv=list(map(str,args));r=subprocess.run(argv,text=True,capture_output=True)
        self.commands.append(dict(argv=argv,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
        if success:self.assertEqual(r.returncode,0,r.stderr)
        return r

    def test_twelve_alpha_fresh_objects_and_explicit_dependencies(self):
        old=Store(ROOT,BASELINE);self.assertEqual(len(old.members()),1164)
        named=named_laws();ids={identity(semantic_entry(v)) for _,v in named}
        self.assertEqual(len(ids),12);self.assertFalse(ids&set(old.members()))
        endpoints={alpha_endpoints(v) for _,v in named}
        for i in old.members():
            p=old.object(i)['payload']
            if 'from' in p and 'node' in p['from']:self.assertNotIn(alpha_endpoints(p),endpoints)
        existing={identity(v) for v in dependency_objects()}
        self.assertTrue(existing<=set(old.members()))
        for name,v in named:
            self.assertEqual(len(v['dependencies']),0 if name.startswith('mapped_arbitrary_') else 2)
            if v['dependencies']:self.assertEqual(len(set(v['dependencies'])&existing),1)

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
    def test_admission_checked_static_certificates_selection_and_batched_typed_outputs(self):
        self.assertEqual(hashlib.sha256(COMPILER.read_bytes()).hexdigest(),'45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08')
        generic=named_laws();store,manifest=publish(self.directory/'generic')
        results=[];scopes=[];certificates=[]
        # Frame files shared across all families/cohorts; no per-run artifacts.
        argfiles={}
        for t in ['u32','i32','u64','f32']:
            argfiles[t]=[]
            for i,args in enumerate(frames(t)):
                p=self.directory/f'args-{t}-{i}.json';p.write_text(json.dumps(args)+'\n');argfiles[t].append((p,args))
        for alternate in [False,True]:
            label='held-out' if alternate else 'primary'
            source=self.directory/(label+'.ink');core=self.directory/(label+'.core.json');subject_path=self.directory/(label+'.semantic.json')
            source.write_text('module Fold17;\n'+'\n'.join(t for _,t in source_functions(alternate))+'\n')
            self.run_command(COMPILER,'emit-core',source,'-o',core)
            self.run_command(COMPILER,'knowledge-check',core,store.root/'view.json')
            self.run_command(COMPILER,'emit-semantic',core,'--core','-o',subject_path)
            subject=json.loads(subject_path.read_text());derived=derive(subject,generic);certificates+=derived
            local=Store.publish(self.directory/(label+'-closure'),dependency_objects()+[semantic_entry(v) for _,v in generic+derived]);local.rebuild()
            roots=[identity(semantic_entry(v)) for _,v in derived];view=self.directory/(label+'-view.json');view.write_bytes(canonical(local.bundle(roots))+b'\n')
            self.run_command(COMPILER,'knowledge-check',core,view)
            apps=[];searches=[]
            for name,text in source_functions(alternate):
                unit=self.directory/f'{label}-{name}.ink';unit.write_text('module Fold17Unit;\n'+text+'\n')
                unit_core=unit.with_suffix('.core.json');selected=unit.with_suffix('.selection.json')
                self.run_command(COMPILER,'emit-core',unit,'-o',unit_core)
                planned=self.run_command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',unit_core,
                    '--knowledge-root',local.root,'--snapshot',local.data/'snapshot.json','--budget',128,'-o',selected)
                searches.append(json.loads(planned.stdout));used=json.loads(selected.read_text())['applications']
                self.assertEqual(len(used),1,(label,name,used));apps+=used
            selection=self.directory/(label+'-selection.json');selection.write_text(json.dumps(dict(schema=1,semantics='ink-evidence-v1',
                input_core_sha256=subject['input_core_sha256'],knowledge=local.bundle(roots),applications=apps),separators=(',',':'))+'\n')
            replay=self.run_command(COMPILER,'check-selection',core,selection)
            selected_core=self.directory/(label+'-selected.core.json');self.run_command(COMPILER,'emit-core',source,'--selection',selection,'-o',selected_core)
            selected_terms=self.directory/(label+'-selected.semantic.json');self.run_command(COMPILER,'emit-semantic',selected_core,'--core','-o',selected_terms)
            terms=json.loads(selected_terms.read_text())['functions'];candidates={identity(semantic_entry(v)):v for _,v in derived}
            for name,_ in source_functions(alternate):
                chosen=next(a for a in apps if a['function']==name);self.assertEqual(terms[name],candidates[chosen['law']]['to'])
                self.assertNotIn('method:map',json.dumps(terms[name]));self.assertNotIn('method:concat',json.dumps(terms[name]));self.assertNotIn('apply',json.dumps(terms[name]))
                t=name.rsplit('_',1)[1]
                for path,args in argfiles[t]:
                    expected,branches=eager_oracle(name,args,alternate);streamed=streamed_oracle(name,args,alternate)
                    if t=='f32' and math.isnan(expected):self.assertTrue(math.isnan(streamed))
                    else:self.assertEqual(bits_or_word(expected,t),bits_or_word(streamed,t))
                    original=json.loads(self.run_command(COMPILER,'run',source,name,path).stdout)
                    actual=json.loads(self.run_command(COMPILER,'run',source,name,path,'--selection',selection).stdout)
                    self.assertEqual(bits_or_word(original,t),bits_or_word(actual,t),(label,name,args))
                    if t=='f32' and math.isnan(expected):self.assertTrue(math.isnan(number(actual)))
                    else:self.assertEqual(bits_or_word(actual,t),bits_or_word(expected,t),(label,name,args))
                    results.append(dict(variant=label,function=name,arguments=args,original=original,selected=actual,
                        expected={'F32Bits':bits_or_word(expected,t)} if t=='f32' and not math.isfinite(expected) else expected,branches=branches))
            scopes.append(dict(variant=label,derived_certificates=len(derived),searches=searches,replay=json.loads(replay.stdout),applications=apps))
        self.assertEqual(len(results),192)
        (self.directory/'interpreter-results.json').write_text(json.dumps(results,indent=2)+'\n')
        (self.directory/'scope.json').write_text(json.dumps(scopes,indent=2)+'\n')
        (self.directory/'certificates.json').write_text(json.dumps(dict(laws=[dict(name=n,law=v) for n,v in certificates]),separators=(',',':'))+'\n')
        name='mapped_prefix_arbitrary_fold_u32';args=[[1,2],[3,4,5],7,3]
        expected=eager_oracle(name,args,False)[0];forward=eager_oracle(name,args,False,False)[0]
        self.assertNotEqual(expected,forward)
        swapped=eager_oracle(name,[args[1],args[0],*args[2:]],False)[0];self.assertNotEqual(expected,swapped)
        (self.directory/'ordered-counterexamples.json').write_text(json.dumps(dict(arguments=args,right=expected,forward=forward,swapped_lists=swapped))+'\n')

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler required')
    def test_hash_valid_wrong_accumulator_and_wrong_concat_order_rejected(self):
        source=self.directory/'source.ink';source.write_text('module FalseFold17;\n'+'\n'.join(t for _,t in source_functions())+'\n');core=source.with_suffix('.core.json')
        self.run_command(COMPILER,'emit-core',source,'-o',core)
        # Break Python producer DAG aliases exactly as the wire encoding does.
        # Otherwise mutating a target Free can also mutate source/proof terms,
        # accidentally creating a valid simultaneous renaming.
        named=dict(named_laws());head=json.loads(json.dumps(named['mapped_arbitrary_fold_u32']))
        head['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']['node']['Op'][1][1]['node']['Bound']=1
        concat=json.loads(json.dumps(named['mapped_prefix_arbitrary_fold_f32']))
        # Preserve a structurally valid composed proof but change the outer
        # traversal to the suffix: the checker must reject its false conclusion.
        concat['to']['node']['Op'][1][0]['node']['Free']='ys'
        for label,candidate in [('head-instead-of-accumulator',head),('suffix-instead-of-prefix',concat)]:
            objects=dependency_objects()+[semantic_entry(v) for _,v in named.items()]+[semantic_entry(candidate)]
            local=Store.publish(self.directory/label,objects);obj=semantic_entry(candidate);view=local.root/'view.json';view.write_bytes(canonical(local.bundle([identity(obj)]))+b'\n')
            rejected=self.run_command(COMPILER,'knowledge-check',core,view,success=False)
            self.assertNotEqual(rejected.returncode,0);self.assertNotIn('identity mismatch',rejected.stderr)
            self.assertNotIn('missing',rejected.stderr.lower());self.assertNotIn('sort mismatch',rejected.stderr.lower())


if __name__=='__main__':unittest.main()
