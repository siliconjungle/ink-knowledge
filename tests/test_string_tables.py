import json
import tempfile
import unittest
from pathlib import Path
from producers.string_tables import candidates
from producers.physical_capabilities import invoke, write
from producers.workspace import compiler_path


class StringTables(unittest.TestCase):
    def test_installed_recipe_is_discoverable_without_planner_dispatch(self):
        from ink_knowledge.recipes import load
        registry, _ = load()
        recipe = next(row for row in registry['recipes'] if row['id'] == 'string-key-dictionaries')
        self.assertEqual(recipe['module'], 'producers.string_tables')
        self.assertEqual(recipe['parameters']['groupings'], ['individual', 'all'])

    def test_typed_sites_compose_and_non_string_roots_reject(self):
        compiler = compiler_path()
        with tempfile.TemporaryDirectory(prefix='ink-dictionary-test-') as temporary:
            directory = Path(temporary)
            source = directory / 'source.ink'
            source.write_text('module dictionaries;state A:Table<String,u32>=Table.empty();state B:Table<String,Bool>=Table.empty();state N:Table<u32,Bool>=Table.empty();query row(k:String)->Option<u32> reads(A){return A.get(k);}')
            core = directory / 'core.json'
            invoke(compiler, 'emit-core', source, '-o', core)
            context = dict(core=json.loads(core.read_bytes()), compiler=str(compiler), emit_target='javascript')
            proposals = list(candidates(context))
            self.assertEqual(len(proposals), 3)
            joint = proposals[-1]['step']['package']
            self.assertEqual(joint['dictionary_tables'], ['A', 'B'])
            self.assertEqual(list(candidates(dict(context, physical=joint))), [])
            selected = proposals[0]['step']['package']
            selected['dictionary_tables'] = ['N']
            with self.assertRaisesRegex(ValueError, 'String keys'):
                invoke(compiler, 'check-physical-plan', source, write(directory / 'invalid.json', selected))
            plan = dict(schema=1, semantics='ink-compiled-plan-v1', input_core_sha256=joint['input_core_sha256'], steps=[dict(kind='physical', package=joint)])
            path = write(directory / 'plan.json', plan)
            invoke(compiler, 'emit-plan', source, path, '--target', 'javascript', '-o', directory / 'module.mjs')
            for target in ['rust', 'rust-wasm', 'wgpu', 'webgpu']:
                with self.assertRaisesRegex(ValueError, 'dictionary tables'):
                    invoke(compiler, 'emit-plan', source, path, '--target', target, '-o', directory / target)
            self.assertEqual(list(candidates(dict(context, emit_target='rust')))[0]['status'], 'declined')


if __name__ == '__main__':
    unittest.main()
