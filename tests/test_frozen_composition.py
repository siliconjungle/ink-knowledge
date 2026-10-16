"""Typed traversal composition is admitted only by complete ordinary proofs."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from producers.fold_chunks import FoldChunks
from producers.frozen_composition import propose_source

ROOT = Path(__file__).resolve().parents[2]
INK = Path(os.environ.get('INK_COMPILER', ROOT/'target/debug/ink')).resolve()
PRODUCER = ROOT/'knowledge/producers/frozen_composition.py'

SOURCE = '''module chunks;
state Code:Table<u64,List<u32>>=Table.empty();
trainable state Weight:Table<u64,u32>=Table.empty();
fn evaluate(code:List<u32>,w:u32,input:u32)->u32{
 return foldl(code,input,fn(op)=>fn(value)=>value*w+op);
}
learn change retune(w:u32)->Unit writes(Weight){Weight.put(0,w);return ();}
adaptive query serve(input:u32)->u32 reads(Code,Weight){
 return evaluate(Code.get(0).unwrap_or([]),Weight.get(0).unwrap_or(1),input);
}
'''


class FrozenComposition(unittest.TestCase):
    def fixture(self, folder, count=32):
        source = folder/'source.ink'; source.write_text(SOURCE)
        core = folder/'core.json'
        subprocess.run([INK, 'emit-core', source, '-o', core], check=True, capture_output=True)
        data = json.loads(core.read_bytes()); data['semantics'] = 'ink-executable-core-v14'
        data['program']['frozen'] = {'Code': [[0, list(range(count))]]}
        core.write_text(json.dumps(data))
        return core, data

    def test_word_fold_uses_typed_helpers_and_complete_action_proofs(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory); core, source = self.fixture(folder)
            plan = folder/'plan.json'
            run = subprocess.run(['python3', PRODUCER, core, '--ink', INK, '-o', plan], capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(json.loads(run.stdout)['helpers'], 7)
            package = json.loads(plan.read_bytes())
            self.assertEqual([step['kind'] for step in package['steps']], ['extension', 'rewrite'])
            rewrite = package['steps'][1]['package']
            self.assertEqual(set(rewrite['action_replacement']['proofs']), {'serve', 'retune'})
            selected = rewrite['action_replacement']['selected']
            self.assertEqual(selected['program']['functions'][:len(source['program']['functions'])], source['program']['functions'])
            # Even after parsing and reserializing the entire plan, dropping a
            # live training action's proof is not admitted as a serving shortcut.
            del rewrite['action_replacement']['proofs']['retune']
            bad = folder/'incomplete.json'; bad.write_text(json.dumps(package))
            result = subprocess.run([INK, 'check-plan', core, bad, '--core'], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('every action proof', result.stderr)

    def test_repeated_word_computation_shares_code_without_caching_results(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory); core, source = self.fixture(folder, 128)
            source['program']['frozen']['Code'][0][1] = list(range(8))*16
            core.write_text(json.dumps(source)); plan = folder/'plan.json'
            run = subprocess.run(['python3', PRODUCER, core, '--ink', INK, '-o', plan], capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(json.loads(run.stdout)['helpers'], 5)
            package = json.loads(plan.read_bytes())
            selected = package['steps'][1]['package']['action_replacement']['selected']
            self.assertEqual(len(selected['program']['functions']), len(source['program']['functions'])+5)
            expanded = folder/'expanded.json'
            run = subprocess.run(['python3',PRODUCER,core,'--ink',INK,'--helper-layout','expanded','-o',expanded],capture_output=True,text=True)
            self.assertEqual(run.returncode,0,run.stderr)
            self.assertEqual(json.loads(run.stdout)['helpers'],31)
            for name, options in [('baseline', []), ('selected', ['--plan', plan]), ('expanded',['--plan',expanded])]:
                command = ([INK, 'compile', core, '--core', *options] if options else
                           [INK, 'build', core, '--core'])
                subprocess.run([*command, '--target', 'javascript', '-o', folder/(name+'.mjs')],
                               check=True, capture_output=True)
            script = folder/'check.mjs'
            script.write_text("""import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
const [a,b,c]=await Promise.all(process.argv.slice(2).map(async p=>(await import(pathToFileURL(p))).createState()));
for(const w of [0,1,0xffffffff,0x80000001]){
 const update=a.invoke('retune',[w]);assert.deepEqual(update,b.invoke('retune',[w]));assert.deepEqual(update,c.invoke('retune',[w]));
 for(const x of [0,1,0xffffffff,0x12345678]){
  let expected=x;for(let i=0;i<128;i++)expected=(Math.imul(expected,w)+(i%8))>>>0;
  const left=a.invoke('serve',[x]),right=b.invoke('serve',[x]);
  assert.deepEqual(left,right);assert.deepEqual(left,c.invoke('serve',[x]));assert.equal(left.result,expected);
  assert.deepEqual(await a.checkpoint(),await b.checkpoint());assert.deepEqual(await a.checkpoint(),await c.checkpoint());
 }
}
""")
            run = subprocess.run(['node',script,folder/'baseline.mjs',folder/'selected.mjs',folder/'expanded.mjs'],capture_output=True,text=True)
            self.assertEqual(run.returncode,0,run.stderr)

    def test_unknown_and_short_traversals_do_not_acquire_helpers(self):
        with tempfile.TemporaryDirectory() as directory:
            _, source = self.fixture(Path(directory), 8)
            _, helpers = propose_source(source)
            self.assertEqual(helpers, [])
            # A missing checked parameter type must not be guessed from the
            # mathematical U64 carrier shared by several source numeric types.
            source['program']['frozen']['Code'][0][1] = list(range(32))
            with patch('producers.frozen_composition.ChunkPartial.known_type', return_value=None):
                _, helpers = propose_source(source)
            self.assertEqual(helpers, [])

    def test_budget_failure_preserves_existing_publication_and_source(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory); _, source = self.fixture(folder)
            original = copy.deepcopy(source)
            with patch.object(FoldChunks, 'MAX_HELPERS', 1):
                with self.assertRaisesRegex(ValueError, 'helper budget'):
                    propose_source(source)
            self.assertEqual(source, original)
            core = folder/'core.json'; core.write_text(json.dumps(source))
            output = folder/'existing.json'; output.write_text('retained previous artifact')
            result = subprocess.run(['python3', PRODUCER, core, '--ink', '/nonexistent/ink', '-o', output], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_text(), 'retained previous artifact')


if __name__ == '__main__':
    unittest.main()
