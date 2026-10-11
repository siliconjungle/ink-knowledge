"""Admission/default search/replay/reification, old809 controls and source oracle."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import random
import struct
import subprocess
import sys
import tempfile
import unittest
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.web_reduction5_laws import named_laws,publish,representative_source
from producers.semantic_laws import var,value,word

ROOT=Path(__file__).resolve().parents[1]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT.parent.parent/'toolchain/ink-sequence-proofs'))
BASELINE='388e3ebd2714c88bc66ae9219102284162f4f65cbed359283f54896b3cfac87c'
FUNCTIONS=('dead_map_fold','discount_total','spread_total','spread_map')


def command(*args):
    return subprocess.run([str(a) for a in args],capture_output=True,text=True,check=True)


def plan(core,store,selected):
    command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',core,
            '--knowledge-root',store.root,'--snapshot',store.data/'snapshot.json','--budget',4096,'-o',selected)
    return json.loads(command(COMPILER,'check-selection',core,selected).stdout)


def oracle():
    spec=importlib.util.spec_from_file_location('reduction5_oracle',ROOT/'research/web-stack-proofs-5/reduction/oracle.py')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def float_bits(x):
    return x['F32Bits'] if isinstance(x,dict) else struct.unpack('<I',struct.pack('<f',x))[0]


class Reduction5LawTests(unittest.TestCase):
    def test_thirteen_new_ids_statements_and_determinism_against_809(self):
        objects=[semantic_entry(law) for _,law in named_laws()]
        ids=[identity(obj) for obj in objects]
        self.assertEqual(len(ids),13)
        self.assertEqual(len(set(ids)),13)
        self.assertEqual(ids,[identity(semantic_entry(law)) for _,law in named_laws()])
        old=Store(ROOT,ROOT/f'store/snapshots/{BASELINE}.json')
        self.assertEqual(len(old.members()),809)
        self.assertFalse(set(ids)&set(old.members()))
        statements={(canonical(obj['payload']['from']),canonical(obj['payload']['to'])) for obj in objects}
        for identifier in old.members():
            obj=old.object(identifier)
            if obj['kind']=='rewrite':
                self.assertNotIn((canonical(obj['payload']['from']),canonical(obj['payload']['to'])),statements)
        self.assertEqual([name for name,_ in named_laws() if name.endswith('_f32')],['ignored_head_fold_f32'])

    def test_literal_word_stages_and_independent_closed_forms(self):
        ref=oracle()
        randoms=random.Random(80905)
        for t in ('u32','i32','u64'):
            bits=64 if t=='u64' else 32
            mask=(1<<bits)-1
            xs=[ref.wrap(x,t) for x in [0,1,mask,mask-2,1<<(bits-1)] + [randoms.getrandbits(bits) for _ in range(12)]]
            for seed,k in ((0,0),(1,1),(ref.wrap(mask-2,t),ref.wrap(mask-4,t))):
                for function in FUNCTIONS:
                    for data in ([],xs[:1],xs):
                        self.assertEqual(ref.original(function,data,seed,k,t),ref.closed(function,data,seed,k,t))

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_all_admitted_and_each_typed_family_default_selected_replayed_reified(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            store,manifest=publish(root/'new')
            for t in ('u32','i32','u64','f32'):
                with self.subTest(type=t):
                    source,core,selected=root/f'{t}.ink',root/f'{t}.json',root/f'{t}.selection.json'
                    source.write_text(representative_source(t))
                    command(COMPILER,'emit-core',source,'-o',core)
                    admitted=json.loads(command(COMPILER,'knowledge-check',core,store.root/'view.json').stdout)
                    self.assertEqual(set(admitted['entries']),set(manifest['names'].values()))
                    receipt=plan(core,store,selected)
                    expected={i for name,i in manifest['names'].items() if name.endswith('_'+t)}
                    self.assertEqual(set(receipt['applied_laws']),expected)
                    command(COMPILER,'emit-core',source,'--selection',selected,'-o',root/f'{t}.selected.json')
                    result=json.loads((root/f'{t}.selected.json').read_text())
                    bodies={f['name']:json.dumps(f['body']) for f in result['program']['functions']}
                    self.assertNotIn('"map"',bodies['dead_map_fold'])
                    self.assertNotIn('"foldr"',bodies['dead_map_fold'])
                    if t!='f32':
                        self.assertNotIn('"map"',bodies['discount_total'])
                        self.assertNotIn('"map"',bodies['spread_total'])

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_prior809_unchanged_union822_has_fresh_law_per_function(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            prior=Store(ROOT,ROOT/f'store/snapshots/{BASELINE}.json')
            objects=[prior.object(i) for i in sorted(prior.members())]
            old=Store.publish(root/'old',objects)
            old.rebuild()
            fresh,manifest=publish(root/'fresh')
            union=Store.publish(root/'union',objects+[fresh.object(i) for i in sorted(fresh.members())])
            union.rebuild()
            source,core=root/'input.ink',root/'input.json'
            source.write_text(representative_source())
            emitted=json.loads(command(COMPILER,'emit-core',source,'-o',core).stdout)
            previous=plan(core,old,root/'old.selection.json')
            self.assertEqual(previous['applied_laws'],[])
            self.assertEqual(previous['selected_core_sha256'],emitted['core_sha256'])
            receipt=plan(core,union,root/'new.selection.json')
            self.assertNotEqual(previous['selected_core_sha256'],receipt['selected_core_sha256'])
            package=json.loads((root/'new.selection.json').read_text())
            for function in FUNCTIONS:
                self.assertTrue({a['law'] for a in package['applications'] if a['function']==function}&set(manifest['names'].values()))

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_hash_valid_false_total_fold_and_factor_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            source,core=root/'input.ink',root/'core.json'
            source.write_text(representative_source())
            command(COMPILER,'emit-core',source,'-o',core)
            laws=dict(named_laws())
            for name in ('discount_total_u32','spread_total_i32','ignored_head_fold_f32','spread_factor_u64'):
                with self.subTest(law=name):
                    forged=copy.deepcopy(laws[name])
                    t=name.rsplit('_',1)[1].upper()
                    if name.startswith('ignored'):
                        from producers.semantic_laws import term
                        forged['to']=term(value('F32'),{'Float':0})
                    else:
                        forged['to']=word(t,0)
                    obj=semantic_entry(forged)
                    store=Store.publish(root/name,[obj])
                    view=store.root/'view.json'
                    view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
                    result=subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True)
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn('semantic normal forms differ',result.stderr)
                    self.assertNotIn('identity mismatch',result.stderr)

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_original_selected_interpreter_empty_boundaries_and_exact_f32_seed(self):
        ref=oracle()
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            store,_=publish(root/'new')
            for t in ('u32','i32','u64','f32'):
                source,core,selected,args=root/'input.ink',root/'core.json',root/'selection.json',root/'args.json'
                source.write_text(representative_source(t))
                command(COMPILER,'emit-core',source,'-o',core)
                plan(core,store,selected)
                if t=='f32':
                    vectors=[[],[-0.0],[1.25,-2.5,16777216.0]]
                    seed,k=-0.0,ref.f32(1.0000001192092896)
                    functions=('dead_map_fold',)
                else:
                    bits=64 if t=='u64' else 32
                    mask=(1<<bits)-1
                    vectors=[[],[ref.wrap(mask,t)],[ref.wrap(x,t) for x in (0,1,mask,mask-2,1<<(bits-1))]]
                    seed,k=ref.wrap(mask-2,t),ref.wrap(mask-4,t)
                    functions=FUNCTIONS
                for xs in vectors:
                    args.write_text(json.dumps([xs,seed,k]))
                    for function in functions:
                        with self.subTest(type=t,function=function,length=len(xs)):
                            original=json.loads(command(COMPILER,'run',source,function,args).stdout)
                            result=json.loads(command(COMPILER,'run',source,function,args,'--selection',selected).stdout)
                            expected=ref.original(function,xs,seed,k,t)
                            if t=='f32':
                                self.assertEqual(float_bits(original),float_bits(expected))
                                self.assertEqual(float_bits(result),float_bits(expected))
                            else:
                                self.assertEqual(original,expected)
                                self.assertEqual(result,expected)
                if t=='f32':
                    for bits in (0x80000000,0x7f800000,0xff800000,0x7fc00019):
                        args.write_text(json.dumps([[{'F32Bits':0x7fc00037}],{'F32Bits':bits},k]))
                        original=json.loads(command(COMPILER,'run',source,'dead_map_fold',args).stdout)
                        result=json.loads(command(COMPILER,'run',source,'dead_map_fold',args,'--selection',selected).stdout)
                        self.assertEqual(float_bits(original),bits)
                        self.assertEqual(float_bits(result),bits)


if __name__=='__main__':
    unittest.main()
