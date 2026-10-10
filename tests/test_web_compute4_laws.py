"""Real admission/replay/reification, immutable786 controls and F32 grouping."""
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
from producers.web_compute4_laws import named_laws,publish,representative_source
from producers.semantic_laws import var,value

ROOT = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER',ROOT.parent.parent/'toolchain/ink-sequence-proofs'))
BASELINE = 'f5ef7bfd79adee16ef47984bd149811cc66dfe7b936820fbd2b68eb0e4170ab9'


def command(*args):
    return subprocess.run([str(a) for a in args],capture_output=True,text=True,check=True)


def plan(core,store,selected):
    command(sys.executable,ROOT.parent/'planner/plan.py','--compiler',COMPILER,'--core',core,
            '--knowledge-root',store.root,'--snapshot',store.data/'snapshot.json','--budget',4096,'-o',selected)
    return json.loads(command(COMPILER,'check-selection',core,selected).stdout)


def oracle():
    spec = importlib.util.spec_from_file_location('compute4_oracle',ROOT/'research/web-stack-proofs-4/compute/oracle.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def float_bits(x):
    return x['F32Bits'] if isinstance(x,dict) else struct.unpack('<I',struct.pack('<f',x))[0]


class Compute4LawTests(unittest.TestCase):
    def test_eleven_new_ids_and_statements_against_immutable786(self):
        objects = [semantic_entry(law) for _,law in named_laws()]
        ids = [identity(obj) for obj in objects]
        self.assertEqual(len(ids),11)
        self.assertEqual(len(set(ids)),11)
        self.assertEqual(ids,[identity(semantic_entry(law)) for _,law in named_laws()])
        old = Store(ROOT,ROOT/f'store/snapshots/{BASELINE}.json')
        self.assertEqual(len(old.members()),786)
        self.assertFalse(set(ids)&set(old.members()))
        statements = {(canonical(obj['payload']['from']),canonical(obj['payload']['to'])) for obj in objects}
        for identifier in old.members():
            obj = old.object(identifier)
            if obj['kind']=='rewrite':
                self.assertNotIn((canonical(obj['payload']['from']),canonical(obj['payload']['to'])),statements)
        floats = [law for name,law in named_laws() if name.endswith('_f32')]
        self.assertEqual(len(floats),2)
        self.assertTrue(all(law['proof']['Induction']['variable']=='xs' for law in floats))

    def test_literal_stage_oracle_word_overflow_empty_and_singletons(self):
        ref = oracle()
        randoms = random.Random(78604)
        for t in ('u32','i32','u64'):
            bits = 64 if t=='u64' else 32
            mask = (1<<bits)-1
            xs = [ref.wrap(x,t) for x in [0,1,mask,mask-2,1<<(bits-1)] + [randoms.getrandbits(bits) for _ in range(12)]]
            for seed,k in ((1,1),(ref.wrap(mask-2,t),ref.wrap(mask-4,t)),(0,0)):
                for function in ('generic_self_zip','zip_then_map','conserved_total'):
                    for data in ([],xs[:1],xs):
                        self.assertEqual(ref.original(function,data,seed,k,t),ref.closed(function,data,seed,k,t))

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_all_admitted_and_all_types_default_selected_replayed_reified(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            store,manifest = publish(root/'new')
            for t in ('u32','i32','u64','f32'):
                with self.subTest(type=t):
                    source,core,selected = root/f'{t}.ink',root/f'{t}.core.json',root/f'{t}.selection.json'
                    source.write_text(representative_source(t))
                    command(COMPILER,'emit-core',source,'-o',core)
                    admitted = json.loads(command(COMPILER,'knowledge-check',core,store.root/'view.json').stdout)
                    self.assertEqual(set(admitted['entries']),set(manifest['names'].values()))
                    receipt = plan(core,store,selected)
                    expected = {i for name,i in manifest['names'].items() if name.endswith('_'+t)}
                    self.assertEqual(set(receipt['applied_laws']),expected)
                    command(COMPILER,'emit-core',source,'--selection',selected,'-o',root/f'{t}.selected.json')
                    result = json.loads((root/f'{t}.selected.json').read_text())
                    body = json.dumps([f['body'] for f in result['program']['functions']])
                    self.assertNotIn('"zip"',body)

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_old786_unchanged_union797_new_application_per_representative(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            prior = Store(ROOT,ROOT/f'store/snapshots/{BASELINE}.json')
            objects = [prior.object(i) for i in sorted(prior.members())]
            old = Store.publish(root/'old',objects)
            old.rebuild()
            fresh,manifest = publish(root/'fresh')
            union = Store.publish(root/'union',objects+[fresh.object(i) for i in sorted(fresh.members())])
            union.rebuild()
            source,core = root/'input.ink',root/'input.core.json'
            source.write_text(representative_source())
            emitted = json.loads(command(COMPILER,'emit-core',source,'-o',core).stdout)
            previous = plan(core,old,root/'old.selection.json')
            self.assertEqual(previous['applied_laws'],[])
            self.assertEqual(previous['selected_core_sha256'],emitted['core_sha256'])
            receipt = plan(core,union,root/'new.selection.json')
            self.assertNotEqual(previous['selected_core_sha256'],receipt['selected_core_sha256'])
            package = json.loads((root/'new.selection.json').read_text())
            for function in ('generic_self_zip','zip_then_map','conserved_total'):
                self.assertTrue({a['law'] for a in package['applications'] if a['function']==function}&set(manifest['names'].values()))

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_hash_valid_false_zip_postmap_and_conservation_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source,core = root/'input.ink',root/'input.core.json'
            source.write_text(representative_source())
            command(COMPILER,'emit-core',source,'-o',core)
            laws = dict(named_laws())
            for name in ('weighted_difference_self_zip_f32','weighted_self_zip_then_map_u32','conserved_weighted_total_u64'):
                with self.subTest(law=name):
                    forged = copy.deepcopy(laws[name])
                    t = name.rsplit('_',1)[1].upper()
                    forged['to'] = var(value(t),'d') if name.startswith('conserved') else var(value({'List':t}),'xs')
                    obj = semantic_entry(forged)
                    store = Store.publish(root/name,[obj])
                    view = store.root/'view.json'
                    view.write_bytes(canonical(store.bundle([identity(obj)]))+b'\n')
                    result = subprocess.run([str(COMPILER),'knowledge-check',str(core),str(view)],capture_output=True,text=True)
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn('semantic normal forms differ',result.stderr)
                    self.assertNotIn('identity mismatch',result.stderr)

    @unittest.skipUnless(COMPILER.is_file(),'frozen compiler absent; set INK_COMPILER')
    def test_original_selected_interpreter_words_and_exact_f32_grouping(self):
        ref = oracle()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            store,_ = publish(root/'new')
            for t in ('u32','i32','u64','f32'):
                source,core,selected,args = root/'input.ink',root/'core.json',root/'selection.json',root/'args.json'
                source.write_text(representative_source(t))
                command(COMPILER,'emit-core',source,'-o',core)
                plan(core,store,selected)
                if t=='f32':
                    vectors = [[],[-0.0],[1.25,-2.5,16777216.0,ref.f32(3.1415927)]]
                    seed,k = 0.25,ref.f32(1.0000001192092896)
                    functions = ('generic_self_zip','zip_then_map')
                else:
                    bits = 64 if t=='u64' else 32
                    mask = (1<<bits)-1
                    vectors = [[],[ref.wrap(mask,t)],[ref.wrap(x,t) for x in (0,1,mask,mask-2,1<<(bits-1))]]
                    seed,k = ref.wrap(mask-2,t),ref.wrap(mask-4,t)
                    functions = ('generic_self_zip','zip_then_map','conserved_total')
                for xs in vectors:
                    args.write_text(json.dumps([xs,seed,k]))
                    for function in functions:
                        with self.subTest(type=t,function=function,length=len(xs)):
                            original = json.loads(command(COMPILER,'run',source,function,args).stdout)
                            result = json.loads(command(COMPILER,'run',source,function,args,'--selection',selected).stdout)
                            expected = ref.original(function,xs,seed,k,t)
                            if t=='f32':
                                self.assertEqual(list(map(float_bits,original)),list(map(float_bits,expected)))
                                self.assertEqual(list(map(float_bits,result)),list(map(float_bits,expected)))
                            else:
                                self.assertEqual(original,expected)
                                self.assertEqual(result,expected)
                if t=='f32':
                    args.write_text(json.dumps([[{'F32Bits':b} for b in (0x80000000,0x7f800000,0xff800000,0x7fc00019)],seed,k]))
                    for function in functions:
                        original = json.loads(command(COMPILER,'run',source,function,args).stdout)
                        result = json.loads(command(COMPILER,'run',source,function,args,'--selection',selected).stdout)
                        self.assertEqual(list(map(float_bits,original)),list(map(float_bits,result)))


if __name__=='__main__':
    unittest.main()
