"""Complete owned graph rewrites need action proofs and retain live parameters."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from producers.fold_chunks import FoldChunks
from producers.frozen_composition import ChunkPartial


class OwnedFrozenGraph(unittest.TestCase):
    def test_complete_owned_graph_and_rehashed_wrong_result(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root/'target/debug/ink')).resolve()
        source = root/'knowledge/tests/fixtures/owned-frozen-source.ink'
        with tempfile.TemporaryDirectory() as temporary:
            d = Path(temporary)
            def run(*args, success=True):
                result = subprocess.run(list(map(str, args)), capture_output=True, text=True, timeout=180)
                self.assertEqual(result.returncode == 0, success, result.stderr[-3000:])
                return result
            core, plan = d/'core.json', d/'plan.json'
            run(compiler, 'emit-core', source, '-o', core)
            data = json.loads(core.read_bytes())
            data['semantics'] = 'ink-executable-core-v14'
            data['program']['frozen'] = dict(Code=[[0, [dict(kind='Kind.Multiply' if i%2 else 'Kind.Add',
                wire=i, weight=i%2) for i in range(32)]]])
            core.write_text(json.dumps(data))
            for width in [1, 2, 4, 8]:
                partial = ChunkPartial(data['program'], owned_chunk_width=width)
                partial.types = dict(input={'List': 'F32'})
                self.assertEqual(partial.known_type({'Call': ['buffer', [{'Var': 'input'}]]}), {'Buffer': 'F32'})
                self.assertEqual(partial.owned_chunk_width, width)
            for constructor, args in [(ChunkPartial, (data['program'],)), (FoldChunks, ({}, []))]:
                with self.assertRaises(ValueError):
                    constructor(*args, owned_chunk_width=3)
            proposed = run('python3', root/'knowledge/producers/frozen_composition.py', core,
                           '--ink', compiler, '-o', plan)
            self.assertIn('checked-proposal', proposed.stdout)
            packet = json.loads(plan.read_bytes())
            replacement = packet['steps'][1]['package']['action_replacement']
            self.assertEqual(len(replacement['proofs']), 3)
            for name, options in [('baseline', []), ('selected', ['--plan', plan])]:
                run(compiler, 'compile' if options else 'build', core, '--core', *options,
                    '--target', 'javascript', '-o', d/(name+'.mjs'))
            script = d/'check.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import {createState as a} from './baseline.mjs';import {createState as b} from './selected.mjs';
const x=a(),y=b();let cases=0;
for(const weight of [[],[0.5,2],[{F32Bits:2147483648},{F32Bits:2141196852}]]){
 assert.deepEqual(x.invoke('retune',[weight]),y.invoke('retune',[weight]));
 for(const input of [[],[1],[{F32Bits:2147483648}],[{F32Bits:2139095040}],[{F32Bits:1}]])
 for(const [call,args] of [['serve',[input]],['frame',[input,false]],['frame',[input,true]]]){
  const before=await x.checkpoint();assert.deepEqual(x.invoke(call,args),y.invoke(call,args));
  assert.deepEqual(await x.checkpoint(),await y.checkpoint());
  if(call==='frame'&&args[1])assert.deepEqual(before,await x.checkpoint());cases++;
 }
}console.log(JSON.stringify({cases,status:'passed'}));''')
            self.assertEqual(json.loads(run('node', script).stdout)['cases'], 45)
            serve = next(a for a in replacement['selected']['program']['actions'] if a['name'] == 'serve')
            serve['body'] = [{'Return': {'Call': ['list', []]}}]
            bad = d/'wrong.json'
            bad.write_text(json.dumps(packet))
            run(compiler, 'check-plan', core, bad, '--core', success=False)


if __name__ == '__main__':
    unittest.main()
