import copy
import json
import tempfile
import shutil
import subprocess
import unittest
from pathlib import Path
from ink_knowledge import Store, identity
from producers.sum_flatten import produce, candidates
from producers.record_elision import produce as produce_records
from ink_knowledge.recipes import load, execute
from producers.physical_capabilities import base, invoke, write
from producers.workspace import compiler_path

def source_text(path, text):
    path.write_text(text)
    return path

class SumFlatten(unittest.TestCase):
    def test_unbounded_and_recursive_leaves_replay_both_directions(self):
        compiler = compiler_path('target/debug/ink')
        with tempfile.TemporaryDirectory(prefix='ink-sum-test-') as temp:
            root = Path(temp)
            source = source_text(root / 'source.ink', 'module codecs;enum Tree{End,Branch(List<Tree>),} fn exact(x:Result<String,Result<Int,u32>>)->Result<String,Result<Int,u32>>{return x;} fn tree(x:Result<Tree,Result<Vec2<f32>,Bool>>)->Result<Tree,Result<Vec2<f32>,Bool>>{return x;}')
            publication = Store.publish(root / 'publication', [])
            layouts = produce(source, compiler, root / 'proofs', publish=publication.root)
            self.assertEqual(len(layouts), 2)
            published = Store(publication.root)
            names = json.loads((published.data / 'names.json').read_bytes())
            for layout in layouts:
                self.assertNotEqual(layout['roundtrip'], layout['inverse'])
                self.assertIn(layout['roundtrip'], published.members())
                self.assertIn(layout['inverse'], names.values())
                invoke(compiler, 'check-sum-codec', source, write(root / 'layout.json', layout))
            missing = copy.deepcopy(layouts[0])
            missing['sum_type'] = {'Result': ['Bool', {'Result': ['Bool', 'Bool']}]}
            with self.assertRaisesRegex(ValueError, 'not declared'):
                invoke(compiler, 'check-sum-codec', source, write(root / 'missing.json', missing))

    def test_rehashed_wrong_tag_proof_does_not_authorize_a_codec(self):
        compiler = compiler_path('target/debug/ink')
        with tempfile.TemporaryDirectory(prefix='ink-sum-false-') as temp:
            root = Path(temp)
            source = source_text(root / 'source.ink', 'module codecs;fn echo(x:Result<u32,Result<u32,u32>>)->Result<u32,Result<u32,u32>>{return x;}')
            layout = produce(source, compiler, root / 'proofs')[0]
            objects = copy.deepcopy(layout['knowledge']['objects'])
            inverse = objects.pop(layout['inverse'])
            conversion = inverse['payload']['declaration']['Theorem']['proof']['Cases']['cases'][0]['proof']['Convert']
            conversion['to']['Construct']['constructor'] = 1
            root_id = identity(inverse)
            self.assertNotEqual(root_id, layout['inverse'])
            objects[root_id] = inverse
            store = Store.publish(root / 'false', list(objects.values()))
            layout['inverse'] = root_id
            layout['knowledge'] = store.bundle([layout['roundtrip'], root_id])
            with self.assertRaises(ValueError):
                invoke(compiler, 'check-sum-codec', source, write(root / 'false-layout.json', layout))

    def test_discovery_retains_contextual_numeric_types_and_local_sums(self):
        compiler = compiler_path('target/debug/ink')
        with tempfile.TemporaryDirectory(prefix='ink-sum-types-') as temp:
            root = Path(temp)
            source = source_text(root / 'source.ink', 'module codecs;fn local(x:u32)->Unit{let r:Result<u32,Result<Bool,String>>=Ok(x);return ();} fn typed()->Result<u32,Result<u32,u32>>{return Ok(0);}')
            schemas = root / 'schemas.json'
            invoke(compiler, 'emit-sum-codecs', source, '-o', schemas)
            types = [s['sum_type'] for s in json.loads(schemas.read_bytes())]
            self.assertIn({'Result':['U32',{'Result':['Bool','String']}]}, types)
            self.assertIn({'Result':['U32',{'Result':['U32','U32']}]}, types)
            self.assertNotIn({'Result':['U64',{'Result':['U64','U64']}]}, types)

    def test_recipe_composition_and_complete_js_boundaries(self):
        compiler = compiler_path('target/debug/ink')
        node = shutil.which('node')
        self.assertIsNotNone(node, 'Node is required for executable sum conformance')
        with tempfile.TemporaryDirectory(prefix='ink-sum-runtime-') as temp:
            root = Path(temp)
            fixture = Path(__file__).parent / 'fixtures'
            source = root / 'source.ink'
            source.write_bytes((fixture / 'sum_runtime.ink').read_bytes())
            core = root / 'source.json'
            invoke(compiler, 'emit-core', source, '-o', core)
            image = json.loads(core.read_bytes())
            registry, _ = load()
            recipe = next(r for r in registry['recipes'] if r['id'] == 'private-sum-spines')
            record_plan = produce_records(source, compiler, root / 'records', ['Box'])
            context = dict(core=image, compiler=str(compiler), emit_target='javascript', physical=record_plan)
            proposals = [r for r in execute(recipe, context) if r['status'] == 'proposal']
            self.assertGreaterEqual(len(proposals), 3)
            joint = proposals[-1]['step']['package']
            self.assertEqual(joint['record_elisions'], record_plan['record_elisions'])
            self.assertEqual(list(candidates(dict(context, physical=joint))), [])
            self.assertEqual(list(candidates(dict(context, emit_target='rust')))[0]['status'], 'declined')
            baseline = dict(schema=1, semantics='ink-compiled-plan-v1', input_core_sha256=joint['input_core_sha256'], steps=[])
            invoke(compiler, 'emit-plan', source, write(root / 'baseline.json', baseline), '--target', 'javascript', '-o', root / 'runtime-ordinary.mjs')
            for index, row in enumerate(proposals):
                physical = row['step']['package']
                plan = dict(schema=1, semantics='ink-compiled-plan-v1', input_core_sha256=physical['input_core_sha256'], steps=[dict(kind='physical', package=physical)])
                name = 'runtime-flat.mjs' if index + 1 == len(proposals) else f'runtime-one-{index}.mjs'
                invoke(compiler, 'emit-plan', source, write(root / 'plan.json', plan), '--target', 'javascript', '-o', root / name)
            (root / 'run.mjs').write_bytes((fixture / 'sum_runtime.mjs').read_bytes())
            result = subprocess.run([node, str(root / 'run.mjs')], capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_physical_admission_executes_on_js_and_rejects_other_backends(self):
        compiler = compiler_path('target/debug/ink')
        with tempfile.TemporaryDirectory(prefix='ink-sum-capability-') as temp:
            root = Path(temp)
            source = source_text(root / 'source.ink', 'module codecs;fn echo(x:Result<u32,Result<u32,u32>>)->Result<u32,Result<u32,u32>>{return x;}')
            layout = produce(source, compiler, root / 'proofs')[0]
            subjects = root / 'subjects.json'
            invoke(compiler, 'emit-bounds-obligations', source, '-o', subjects)
            physical = base(json.loads(subjects.read_bytes())['source'])
            physical['sum_spines'] = [layout]
            path = write(root / 'physical.json', physical)
            invoke(compiler, 'check-physical-plan', source, path)
            plan = write(root / 'plan.json', {'schema':1,'semantics':'ink-compiled-plan-v1','input_core_sha256':physical['input_core_sha256'],'steps':[{'kind':'physical','package':physical}]})
            invoke(compiler, 'check-plan', source, plan)
            invoke(compiler,'emit-plan',source,plan,'--target','javascript','-o',root/'javascript.mjs')
            for target in ['rust','c','rust-wasm','c-wasm','wgpu','webgpu']:
                with self.assertRaisesRegex(ValueError, 'sum spine'):
                    invoke(compiler, 'emit-plan', source, plan, '--target', target, '-o', root / target)

if __name__ == '__main__':
    unittest.main()
