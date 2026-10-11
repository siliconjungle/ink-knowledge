"""Static arithmetic admission, pinned novelty and executable selection checks."""
import atexit
import copy
import importlib.util
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import binary,word
from producers.web_compute13_laws import named_laws,publish,representative_source

TRACE=[]
FRAMES=[]

def archive_trace():
    path=os.environ.get("INK_COMPUTE13_RECEIPTS")
    if path:Path(path).write_text(json.dumps(dict(commands=TRACE,interpreter_frames=FRAMES),indent=2)+"\n")

atexit.register(archive_trace)

ROOT=Path(__file__).resolve().parents[1]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT.parent.parent/'toolchain/ink-sequence-proofs'))
BASELINE='a7ca4c89c1f610ee997319a7e13601b263ee187515ecb5e0f7a506cb40c6636c'
FUNCTIONS=('mixed_prefix6','mixed_prefix12','mixed_prefix24')


def command(*args):
    r=subprocess.run([str(a) for a in args],capture_output=True,text=True)
    TRACE.append(dict(command=[str(a) for a in args],exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr))
    r.check_returncode()
    return r


def plan(core,store,selected):
    command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,
            '--core',core,'--knowledge-root',store.root,'--snapshot',store.data/'snapshot.json',
            '--budget',4096,'-o',selected)
    return json.loads(command(COMPILER,'check-selection',core,selected).stdout)


def oracle():
    spec=importlib.util.spec_from_file_location('compute13_oracle',ROOT/'research/web-stack-proofs-13/compute/oracle.py')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class Compute13LawTests(unittest.TestCase):
    def test_nine_deterministic_fresh_static_word_statements(self):
        entries=[semantic_entry(candidate) for _,candidate in named_laws()]
        ids=[identity(obj) for obj in entries]
        self.assertEqual(len(ids),9)
        self.assertEqual(len(set(ids)),9)
        self.assertEqual(ids,[identity(semantic_entry(candidate)) for _,candidate in named_laws()])
        old=Store(ROOT,ROOT/f'store/snapshots/{BASELINE}.json')
        self.assertEqual(len(old.members()),977)
        self.assertFalse(set(ids)&set(old.members()))
        statements={(canonical(obj['payload']['from']),canonical(obj['payload']['to'])) for obj in entries}
        for identifier in old.members():
            obj=old.object(identifier)
            if obj['kind']=='rewrite':
                self.assertNotIn((canonical(obj['payload']['from']),canonical(obj['payload']['to'])),statements)
        self.assertNotIn('F32',json.dumps(entries))
        self.assertNotIn('repeat',json.dumps(entries))

    def test_independent_literal_stages_match_unbounded_closed_oracle(self):
        reference=oracle()
        rng=random.Random(97707)
        for t in ('u32','i32','u64'):
            bits=64 if t=='u64' else 32
            mask=(1<<bits)-1
            values=[reference.native(v,t) for v in [0,1,2,mask,mask-2,1<<(bits-1)]+[rng.getrandbits(bits) for _ in range(32)]]
            for seed in (0,1,reference.native(mask-2,t),reference.native(1<<(bits-1),t)):
                for k in (0,1,reference.native(mask,t),reference.native(mask-2,t)):
                    for function in FUNCTIONS:
                        self.assertEqual(reference.original(function,values,seed,k,t),reference.closed(function,values,seed,k,t))
                        self.assertEqual(reference.original(function,[],seed,k,t),[])
                        self.assertEqual(reference.compact(function,values,seed,k,t),reference.closed(function,values,seed,k,t))
                        self.assertEqual(reference.recurrence(function,values,seed,k,t),reference.closed(function,values,seed,k,t))
            for k in (7,reference.native(mask-2,t)):
                for function in FUNCTIONS:
                    self.assertGreater(len(set(reference.compact(function,list(range(8)),1,k,t))),1)

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_all_admitted_and_all_types_default_selected_replayed_reified(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            store,manifest=publish(root/'new')
            for t in ('u32','i32','u64'):
                with self.subTest(type=t):
                    source,core,selection=root/f'{t}.ink',root/f'{t}.core.json',root/f'{t}.selection.json'
                    source.write_text(representative_source(t))
                    command(COMPILER,'emit-core',source,'-o',core)
                    checked=json.loads(command(COMPILER,'knowledge-check',core,store.root/'view.json').stdout)
                    self.assertEqual(set(checked['entries']),set(manifest['names'].values()))
                    receipt=plan(core,store,selection)
                    expected={i for name,i in manifest['names'].items() if name.endswith('_'+t)}
                    self.assertEqual(set(receipt['applied_laws']),expected)
                    command(COMPILER,'emit-core',source,'--selection',selection,'-o',root/f'{t}.selected.core.json')
                    functions=json.loads((root/f'{t}.selected.core.json').read_text())['program']['functions']
                    self.assertEqual(len(functions),3)
                    for function in FUNCTIONS:
                        body=next(f['body'] for f in functions if f['name']==function)
                        self.assertEqual(json.dumps(body).count('"Let"'),FUNCTIONS.index(function)+2)
                    self.assertNotIn('repeat',json.dumps(functions))
                    applications=json.loads(selection.read_text())['applications']
                    for function in FUNCTIONS:
                        self.assertEqual({a['law'] for a in applications if a['function']==function},{manifest['names'][function+'_'+t]})

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_old977_unchanged_union986_selects_new_law_per_function(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            old=Store(ROOT,ROOT/f'store/snapshots/{BASELINE}.json')
            objects=[old.object(i) for i in sorted(old.members())]
            isolated=Store.publish(root/'old',objects);isolated.rebuild()
            fresh,manifest=publish(root/'fresh')
            union=Store.publish(root/'union',objects+[fresh.object(i) for i in sorted(fresh.members())]);union.rebuild()
            for t in ('u32','i32','u64'):
                with self.subTest(type=t):
                    source,core=root/f'{t}.ink',root/f'{t}.core.json'
                    source.write_text(representative_source(t))
                    emitted=json.loads(command(COMPILER,'emit-core',source,'-o',core).stdout)
                    prior=plan(core,isolated,root/f'{t}.old.selection.json')
                    self.assertEqual(prior['applied_laws'],[])
                    self.assertEqual(prior['selected_core_sha256'],emitted['core_sha256'])
                    receipt=plan(core,union,root/f'{t}.new.selection.json')
                    self.assertNotEqual(prior['selected_core_sha256'],receipt['selected_core_sha256'])
                    package=json.loads((root/f'{t}.new.selection.json').read_text())
                    for function in FUNCTIONS:
                        self.assertEqual({a['law'] for a in package['applications'] if a['function']==function},{manifest['names'][function+'_'+t]})

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_three_hash_valid_false_static_identities_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            source,core=root/'source.ink',root/'core.json'
            source.write_text(representative_source())
            command(COMPILER,'emit-core',source,'-o',core)
            candidates=dict(named_laws())
            for name,t in (('mixed_prefix6_u32','U32'),('mixed_prefix12_i32','I32'),('mixed_prefix24_u64','U64')):
                with self.subTest(law=name):
                    forged=copy.deepcopy(candidates[name])
                    forged['to']=binary('+',forged['to'],word(t,1))
                    obj=semantic_entry(forged)
                    store=Store.publish(root/name,[obj])
                    view=store.root/'view.json'
                    view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
                    result=subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True)
                    TRACE.append(dict(command=[str(COMPILER),'knowledge-check',str(core),str(view)],exit_code=result.returncode,stdout=result.stdout,stderr=result.stderr))
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn('semantic normal forms differ',result.stderr)
                    self.assertNotIn('identity mismatch',result.stderr)

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_actual_original_and_selected_all_types_boundary_random_and_empty(self):
        reference=oracle()
        rng=random.Random(97770)
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            store,_=publish(root/'new')
            for t in ('u32','i32','u64'):
                bits=64 if t=='u64' else 32
                mask=(1<<bits)-1
                boundary=[reference.native(x,t) for x in (0,1,2,mask,mask-2,1<<(bits-1))]
                randoms=[reference.native(rng.getrandbits(bits),t) for _ in range(10)]
                source,core,selection=root/'input.ink',root/'input.json',root/'selection.json'
                source.write_text(representative_source(t))
                command(COMPILER,'emit-core',source,'-o',core)
                plan(core,store,selection)
                fixtures=[([],0,0),(boundary,1,0),(boundary,reference.native(mask-2,t),reference.native(mask,t)),(randoms,reference.native(1<<(bits-1),t),reference.native(mask-2,t))]
                for xs,seed,k in fixtures:
                    args=root/'args.json';args.write_text(json.dumps([xs,seed,k]))
                    for function in FUNCTIONS:
                        with self.subTest(type=t,function=function,args=[xs,seed,k]):
                            expected=reference.closed(function,xs,seed,k,t)
                            original=json.loads(command(COMPILER,'run',source,function,args).stdout)
                            selected=json.loads(command(COMPILER,'run',source,function,args,'--selection',selection).stdout)
                            FRAMES.append(dict(type=t,function=function,args=[xs,seed,k],expected=expected,original=original,selected=selected))
                            self.assertEqual(original,expected)
                            self.assertEqual(selected,expected)


if __name__=='__main__':unittest.main()
