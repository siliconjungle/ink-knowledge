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
    def test_residual_workload_folds_and_result_helpers_keep_runtime_state(self):
        source = '''module residual_computation;
record Item { x:u32, y:u32, }
state Code:Table<u64,List<u32>>=Table.empty();
state Weight:Table<u64,u32>=Table.empty();
state Count:Table<u64,u32>=Table.empty();
event advanced:u32;
fn evaluate(code:List<u32>,w:u32,b:u32,input:u32)->u32 {
 return foldl(code,input,fn(op)=>fn(value)=>choose(op==0,value*w,value+b));
}
fn total(items:List<Item>,code:List<u32>,w:u32)->u32 {
 return foldl(items,0,fn(item)=>fn(sum)=>sum+evaluate(code,w,3,item.x)+evaluate(code,2,w,item.y));
}
fn accepted(mode:u32,value:u32)->Result<u32,String> {
 if mode==0 {return Ok(value);}return Err("mode");
}
change advance(fail:Bool)->Result<u32,String> reads(Count) writes(Count) emits(advanced) {
 let count=Count.get(0).unwrap_or(0)+1;Count.put(0,count);emit advanced(count);
 if fail {return Err("argument");}return Ok(count);
}
change guarded(fail:Bool)->Result<u32,String> reads(Count) writes(Count) emits(advanced) {
 return accepted(0,advance(fail)?) ;
}
change retune(w:u32)->Unit writes(Weight){Weight.put(0,w);return ();}
query loss(items:List<Item>)->u32 reads(Code,Weight) {
 return total(items,Code.get(0).unwrap_or([]),Weight.get(0).unwrap_or(1));
}
'''
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory);src=folder/'source.ink';src.write_text(source)
            core=folder/'core.json'
            emitted=subprocess.run([INK,'emit-core',src,'-o',core],capture_output=True,text=True)
            self.assertEqual(emitted.returncode,0,emitted.stderr)
            data=json.loads(core.read_bytes());data['semantics']='ink-executable-core-v14'
            data['program']['frozen']={'Code':[[0,[0,1]*16]]};core.write_text(json.dumps(data))
            plan=folder/'plan.json'
            proposed=subprocess.run(['python3',PRODUCER,core,'--ink',INK,'-o',plan],capture_output=True,text=True)
            self.assertEqual(proposed.returncode,0,proposed.stderr)
            from ink_knowledge import Store, identity
            from ink_knowledge.store import operations
            objects=json.loads(plan.read_bytes())['steps'][1]['package']['knowledge']['objects']
            laws=[o for o in objects.values() if o['kind']=='theorem'
                and 'GeneralizedInduction' in o['payload']['declaration']['Theorem']['proof']
                and o['payload']['declaration']['Theorem']['params'][0][0].startswith('equivalent_rows_')]
            self.assertTrue(laws,'residual workload traversal needs a universal fold equation')
            law=laws[0]
            for name,mutate in [
                ('wrong_accumulator',lambda t:t['to']['Call']['arguments'].__setitem__(-1,{'U64':1})),
                ('wrong_scope',lambda t:t['proof']['GeneralizedInduction']['cases'][1].__setitem__('proof',{'Hypothesis':999})),
            ]:
                bad=copy.deepcopy(law);mutate(bad['payload']['declaration']['Theorem'])
                bad['interface']['operations']=operations(bad['payload'])
                forged=Store.publish(folder/name,[*objects.values(),bad]);view=folder/(name+'.json')
                view.write_text(json.dumps(forged.bundle([identity(bad)])))
                rejected=subprocess.run([INK,'knowledge-check',core,view],capture_output=True,text=True)
                self.assertNotEqual(rejected.returncode,0)
                self.assertNotIn('identity mismatch',rejected.stderr)
                self.assertNotIn('interface mismatch',rejected.stderr)
            for name,command in [('baseline',[INK,'build',core,'--core']),
                                 ('selected',[INK,'compile',core,'--core','--plan',plan])]:
                compiled=subprocess.run([*command,'--target','javascript','-o',folder/(name+'.mjs')],capture_output=True,text=True)
                self.assertEqual(compiled.returncode,0,compiled.stderr)
            script=folder/'execute.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
const [a,b]=await Promise.all(process.argv.slice(2).map(async p=>(await import(pathToFileURL(p))).createState()));
function evalCode(w,b,x){for(let i=0;i<16;i++)x=(Math.imul(x,w)+b)>>>0;return x;}
for(const w of [0,1,0x80000001,0xffffffff]){
 assert.deepEqual(a.invoke('retune',[w]),b.invoke('retune',[w]));
 for(const rows of [[],[{x:3,y:7}],[{x:0xffffffff,y:1},{x:42,y:0x80000000}]]){
  let expected=0;for(const r of rows)expected=(expected+evalCode(w,3,r.x)+evalCode(2,w,r.y))>>>0;
  const result=a.invoke('loss',[rows]);assert.deepEqual(result,b.invoke('loss',[rows]));assert.equal(result.result,expected);
 }
}
for(const fail of [false,true,false]){
 const before=await a.checkpoint();assert.deepEqual(a.invoke('guarded',[fail]),b.invoke('guarded',[fail]));
 assert.deepEqual(await a.checkpoint(),await b.checkpoint());
 if(fail)assert.deepEqual(await a.checkpoint(),before);
}
''')
            executed=subprocess.run(['node',script,folder/'baseline.mjs',folder/'selected.mjs'],capture_output=True,text=True)
            self.assertEqual(executed.returncode,0,executed.stderr)

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

    def test_suffix_parametric_laws_scale_and_reject_a_rehashed_false_tail_claim(self):
        from ink_knowledge import Store, identity
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory);core,source=self.fixture(folder,512)
            source['program']['frozen']['Code'][0][1]=list(range(8))*64
            core.write_text(json.dumps(source));plan=folder/'plan.json'
            run=subprocess.run(['python3',PRODUCER,core,'--ink',INK,'-o',plan],capture_output=True,text=True)
            self.assertEqual(run.returncode,0,run.stderr)
            self.assertEqual(json.loads(run.stdout)['helpers'],7)
            objects=json.loads(plan.read_bytes())['steps'][1]['package']['knowledge']['objects']
            universal=[o for o in objects.values() if o['kind']=='theorem'
                and o['payload']['declaration']['Theorem']['params']
                and o['payload']['declaration']['Theorem']['params'][0][0]=='chunk_suffix']
            self.assertEqual(len(universal),7)
            # Check one ordinary universal lemma independently of the action
            # plan, then publish a well-typed false conclusion under a new ID.
            law=next(o for o in universal if 'Construct' in objects[
                o['payload']['declaration']['Theorem']['from']['Call']['arguments'][0]['Call']['function']
            ]['payload']['declaration']['Function']['body'])
            view=folder/'view.json'
            store=Store.publish(folder/'valid',list(objects.values()))
            view.write_text(json.dumps(store.bundle([identity(law)])))
            valid=subprocess.run([INK,'knowledge-check',core,view],capture_output=True,text=True)
            self.assertEqual(valid.returncode,0,valid.stderr)
            bad=copy.deepcopy(law);theorem=bad['payload']['declaration']['Theorem']
            theorem['to']=theorem['to']['Call']['arguments'][-1]
            forged=Store.publish(folder/'forged',[*objects.values(),bad])
            view.write_text(json.dumps(forged.bundle([identity(bad)])))
            rejected=subprocess.run([INK,'knowledge-check',core,view],capture_output=True,text=True)
            self.assertNotEqual(rejected.returncode,0)
            self.assertNotIn('identity mismatch',rejected.stderr)
            self.assertNotIn('interface mismatch',rejected.stderr)
            self.assertTrue('proof' in rejected.stderr or 'resource limit' in rejected.stderr,rejected.stderr)
            for name,command in [('baseline',[INK,'build',core,'--core']),
                                 ('selected',[INK,'compile',core,'--core','--plan',plan])]:
                subprocess.run([*command,'--target','javascript','-o',folder/(name+'.mjs')],check=True,capture_output=True)
            script=folder/'execute.mjs'
            script.write_text("""import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
const [a,b]=await Promise.all(process.argv.slice(2).map(async p=>(await import(pathToFileURL(p))).createState()));
for(const w of [0,1,0xffffffff,0x80000001]){
 assert.deepEqual(a.invoke('retune',[w]),b.invoke('retune',[w]));
 for(const x of [0,1,0xffffffff,0x12345678]){
  let expected=x;for(let i=0;i<512;i++)expected=(Math.imul(expected,w)+i%8)>>>0;
  const left=a.invoke('serve',[x]);assert.deepEqual(left,b.invoke('serve',[x]));assert.equal(left.result,expected);
  assert.deepEqual(await a.checkpoint(),await b.checkpoint());
 }
}
""")
            executed=subprocess.run(['node',script,folder/'baseline.mjs',folder/'selected.mjs'],capture_output=True,text=True)
            self.assertEqual(executed.returncode,0,executed.stderr)

    def test_identity_steps_consume_full_chunks_and_the_short_final_chunk(self):
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory)
            src=folder/'identity.ink';src.write_text("""module identity_prefix;
state Code:Table<u64,List<u32>>=Table.empty();
fn evaluate(code:List<u32>,input:u32)->u32{return foldl(code,input,fn(op)=>fn(value)=>value);}
query serve(input:u32)->u32 reads(Code){return evaluate(Code.get(0).unwrap_or([]),input);}
""")
            core=folder/'core.json'
            subprocess.run([INK,'emit-core',src,'-o',core],check=True,capture_output=True)
            source=json.loads(core.read_bytes());source['program']['frozen']={'Code':[[0,list(range(67))]]}
            source['semantics']='ink-executable-core-v14';core.write_text(json.dumps(source))
            plan=folder/'plan.json'
            result=subprocess.run(['python3',PRODUCER,core,'--ink',INK,'-o',plan],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr)

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
