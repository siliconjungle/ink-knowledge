"""Universal chunk transition laws and a discharged concrete wrapping instance."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class ChunkLaws(unittest.TestCase):
    def test_bulk_instance_needs_preservation_and_matches_literal_execution(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
        source=root/'knowledge/libraries/chunk-laws.ink'
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            def run(*arguments,success=True):
                result=subprocess.run(list(map(str,arguments)),capture_output=True,text=True,timeout=120)
                if success:self.assertEqual(result.returncode,0,result.stderr[-3000:])
                else:self.assertNotEqual(result.returncode,0)
                return result
            receipt=json.loads(run(compiler,'emit-laws',source,'-o',directory/'proofs.json').stdout)
            self.assertEqual(set(receipt['names']),{'foldl_append','flatten_fold','foldl_state','foldl_steps','bulk_chunks','sum_chunk','bulk_sum'})
            original=source.read_text()
            for index,text in enumerate([
                original.replace('assuming(use sum_chunk(__assumed_chunk,__assumed_current))',''),
                original.replace('bulk_chunks<u64,u64>(chunks,state,fn(value,acc)=>acc+value,fn(chunk,acc)=>acc+sum(chunk))',
                                 'bulk_chunks<u64,u64>(chunks,state,fn(value,acc)=>acc+value,fn(chunk,acc)=>acc+sum(chunk)+1)'),
            ]):
                bad=directory/f'bad-{index}.ink';bad.write_text(text)
                result=run(compiler,'emit-laws',bad,'-o',directory/f'bad-{index}.json',success=False)
                self.assertIn('law bulk_sum:',result.stderr)
            run(compiler,'build',root/'examples/crdts/chunked_transitions.ink',
                '--target','javascript','-o',directory/'compiled.mjs')
            script=directory/'verify.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import {functions} from './compiled.mjs';
for(const blocks of [[],[[]],[[1n,2n],[3n]],[[0xffffffffffffffffn],[1n]],[[7n],[],[9n,11n]]]){
 for(const initial of [0n,9007199254740993n,0xffffffffffffffffn]){
  const expected=BigInt.asUintN(64,blocks.flat().reduce((a,b)=>a+b,initial));
  assert.deepEqual(functions.compare(blocks,initial),{flattened:expected,chunked:expected,bulk:expected});
 }
}
''')
            run('node',script)


if __name__=='__main__':unittest.main()
