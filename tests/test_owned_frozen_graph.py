"""Complete owned graph rewrites need action proofs and retain live parameters."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from producers.fold_chunks import FoldChunks
from producers.frozen_composition import ChunkPartial
from ink_knowledge import Store, canonical
from ink_knowledge.recipes import execute, load


class OwnedFrozenGraph(unittest.TestCase):
    def test_complete_owned_graph_and_rehashed_wrong_result(self):
        self.check_graph(project=False)

    def test_projected_owner_composes_with_frozen_balanced_helpers(self):
        self.check_graph(project=True)

    def check_graph(self, *, project):
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
            composition_source = core
            projection = None
            if project:
                sid = json.loads(run(compiler, 'check-core', core).stdout)['core_sha256']
                store = Store.publish(d/'knowledge', [])
                registry, _ = load(store=store)
                recipe = next(r for r in registry['recipes'] if r['id'] == 'fold-state-projection')
                proposals = list(execute(recipe, dict(core=data, source=sid, compiler=str(compiler),
                    knowledge_root=str(store.root), knowledge_snapshot=store.snapshot_id, check_timeout=180)))
                self.assertEqual(len(proposals), 1, proposals)
                self.assertEqual(proposals[0]['status'], 'proposal', proposals)
                projection = dict(schema=1, semantics='ink-compiled-plan-v1',
                    input_core_sha256=sid, steps=proposals[0]['steps'])
                path = d/'projection.json'; path.write_bytes(canonical(projection))
                checked = json.loads(run(compiler, 'check-plan', core, path, '--core').stdout)
                composition_source = d/'projected.json'
                composition_source.write_bytes(canonical(checked['state']['core']))
            proposed = run('python3', root/'knowledge/producers/frozen_composition.py', composition_source,
                           '--ink', compiler, '-o', plan)
            self.assertIn('checked-proposal', proposed.stdout)
            packet = json.loads(plan.read_bytes())
            replacement = packet['steps'][1]['package']['action_replacement']
            self.assertEqual(len(replacement['proofs']), 3)
            if project:
                self.assertTrue(any(f['result'] == {'Buffer': 'F32'}
                    for f in replacement['selected']['program']['functions']))
                packet = dict(projection, steps=projection['steps'] + packet['steps'])
                plan.write_bytes(canonical(packet))
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
