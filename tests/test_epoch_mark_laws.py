"""Epoch decoder component proofs use the actual checked record declaration."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class EpochMarkLaws(unittest.TestCase):
    def test_schema_selection_and_false_component_proofs(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
        source=root/'knowledge/libraries/epoch-mark-laws.ink'
        spec=importlib.util.spec_from_file_location('epoch_author',root/'tools/epoch_mark_laws.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        with self.assertRaises(ValueError):module.authored({'program':{'records':{'Bad':[['epoch','U32'],['flag','U64']]}}})
        with self.assertRaises(ValueError):module.authored({'program':{'records':{'Bad;extra':[['epoch','U32'],['flag','U32']]}}})
        renamed=module.authored({'program':{'records':{'CacheCell':[['stamp','U32'],['value','U32']]}}},tag='stamp',value='value')
        self.assertIn('record CacheCell{stamp:u32,value:u32,}',renamed)
        with tempfile.TemporaryDirectory()as temporary:
            directory=Path(temporary)
            def run(*args,success=True):
                result=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=120)
                if success:self.assertEqual(result.returncode,0,result.stderr[-3000:])
                else:self.assertNotEqual(result.returncode,0)
                return result
            receipt=json.loads(run(compiler,'emit-laws',source,'-o',directory/'proofs.json').stdout)
            self.assertEqual(set(receipt['names']),{'fresh','stale','written_current','empty_any_generation','reset_decoded','map_append','push_decoded'})
            changed=directory/'renamed.ink';changed.write_text(renamed)
            run(compiler,'emit-laws',changed,'-o',directory/'renamed.json')
            original=source.read_text()
            for index,bad in enumerate([
                original.replace(' requires current: (mark.epoch==generation)==true;',''),
                original.replace('epoch:0,flag:0','epoch:0,flag:1'),
                original.replace('buffer.push(mark).freeze()','buffer.freeze()'),
            ]):
                changed=directory/f'bad-{index}.ink';changed.write_text(bad)
                result=run(compiler,'emit-laws',changed,'-o',directory/f'bad-{index}.json',success=False)
                self.assertIn('law ',result.stderr)


if __name__=='__main__':unittest.main()
