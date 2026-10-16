"""Mutable graph staging retains live inputs and its generic fallback."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import canonical
from producers.function_specialization import propose_source


class FunctionSpecialization(unittest.TestCase):
    def test_mutable_owned_graph_and_wrong_source_rejects(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root/'target/debug/ink')).resolve()
        code = [dict(kind='Kind.Multiply' if i % 2 else 'Kind.Add', wire=i, weight=i % 2)
                for i in range(32)]
        literal = '[' + ','.join('Node{kind:%s,wire:%d,weight:%d}' %
                                (n['kind'], n['wire'], n['weight']) for n in code) + ']'
        source = (root/'knowledge/tests/fixtures/owned-frozen-source.ink').read_text()
        source = source.replace('return evaluate(Code.get', 'return adaptive(Code.get')
        source = source.replace('let result=evaluate(Code.get', 'let result=adaptive(Code.get')
        source += '\nfn chosen(weights:List<f32>,input:List<f32>)->List<f32>{return evaluate(' + literal + ',weights,input);}\n'
        source += 'fn adaptive(code:List<Node>,weights:List<f32>,input:List<f32>)->List<f32>{return choose(code==' + literal + ',chosen(weights,input),evaluate(code,weights,input));}\n'
        source += 'change recode(code:List<Node>)->Unit writes(Code){Code.put(0,code);return ();}\n'
        with tempfile.TemporaryDirectory() as temporary:
            d = Path(temporary)
            def run(*args, success=True):
                result = subprocess.run(list(map(str, args)), capture_output=True, text=True, timeout=240)
                self.assertEqual(result.returncode == 0, success, result.stderr[-4000:])
                return result
            path = d/'source.ink'; path.write_text(source)
            core = d/'core.json'; plan = d/'plan.json'
            run(compiler, 'emit-core', path, '-o', core)
            original = json.loads(core.read_bytes())
            selected, helpers, changed = propose_source(original, ['chosen'])
            self.assertEqual(changed, ['chosen'])
            self.assertTrue(helpers)
            self.assertEqual(original.get('program', {}).get('frozen', {}), {})
            with self.assertRaises(ValueError):
                propose_source(original, [])
            with self.assertRaises(ValueError):
                propose_source(original, ['missing'])
            proposed = run('python3', root/'knowledge/producers/function_specialization.py', core,
                           '--functions', 'chosen', '--ink', compiler, '-o', plan)
            self.assertIn('checked-proposal', proposed.stdout)
            packet = json.loads(plan.read_bytes())
            self.assertEqual([s['kind'] for s in packet['steps']], ['extension', 'functions'])
            replacement = packet['steps'][-1]['package']
            self.assertEqual(list(replacement['proofs']), ['chosen'])
            self.assertEqual(replacement['selected']['program']['actions'], original['program']['actions'])
            self.assertEqual(replacement['selected']['program'].get('frozen', {}), {})
            for name, options in [('baseline', []), ('selected', ['--plan', plan])]:
                run(compiler, 'compile' if options else 'build', core, '--core', *options,
                    '--target', 'javascript', '-o', d/(name+'.mjs'))
            (d/'code.json').write_text(json.dumps(code))
            (d/'check.mjs').write_text('''import assert from 'node:assert/strict';
import fs from 'node:fs';
import {createState as a} from './baseline.mjs';import {createState as b} from './selected.mjs';
const code=JSON.parse(fs.readFileSync(new URL('./code.json',import.meta.url),'utf8'));
const x=a(),y=b();let cases=0;
function invoke(name,args){assert.deepEqual(x.invoke(name,args),y.invoke(name,args));cases++;}
const changed=structuredClone(code);changed[0].kind='Kind.Multiply';
for(const graph of [code,[],[{kind:'Kind.Add',wire:4294967295,weight:0}],changed,code]){
 invoke('recode',[graph]);
 for(const weights of [[],[0.5,2],[{F32Bits:2147483648},{F32Bits:2141196852}]]){
  invoke('retune',[weights]);
  for(const input of [[],[1],[{F32Bits:2147483648}],[{F32Bits:1}]])
  for(const [name,args] of [['serve',[input]],['frame',[input,false]],['frame',[input,true]]]){
   const before=await x.checkpoint();invoke(name,args);
   assert.deepEqual(await x.checkpoint(),await y.checkpoint());
   if(name==='frame'&&args[1])assert.deepEqual(before,await x.checkpoint());
  }
 }
 const state=await x.checkpoint();await x.restore(state);await y.restore(state);
 assert.deepEqual(await x.checkpoint(),await y.checkpoint());
}console.log(JSON.stringify({cases,status:'passed'}));''')
            self.assertEqual(json.loads(run('node', d/'check.mjs').stdout)['cases'], 200)
            bad = json.loads(canonical(packet))
            chosen = next(f for f in bad['steps'][-1]['package']['selected']['program']['functions']
                          if f['name'] == 'chosen')
            chosen['body'] = {'Call': ['list', []]}
            wrong = d/'wrong.json'; wrong.write_bytes(canonical(bad))
            run(compiler, 'check-plan', core, wrong, '--core', success=False)


if __name__ == '__main__':
    unittest.main()
