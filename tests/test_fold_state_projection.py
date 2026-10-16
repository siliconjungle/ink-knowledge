"""Universal source-fold projection, checked owners, and false simulations."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_knowledge.recipes import execute, load
from producers.fold_state_projection import candidates, prove


SOURCE = '''module projected_graph;
record Work { values:Buffer<u32>, total:u32, }
fn step(item:u32,weight:u32,work:Work)->Work {
 let value=work.values.at_or(item,0)+weight;
 return Work{values:work.values.push(value),total:work.total+value};
}
fn evaluate(code:List<u32>,weight:u32,input:List<u32>)->List<u32> {
 let work=foldl(code,Work{values:buffer(input),total:0},fn(item)=>fn(work)=>step(item,weight,work));
 return work.values.freeze();
}
state Weight:Table<u64,u32>=Table.empty();
state Count:Table<u64,u32>=Table.empty();
event advanced:u32;
change retune(weight:u32)->Unit writes(Weight){Weight.put(0,weight);return ();}
query serve(code:List<u32>,input:List<u32>)->List<u32> reads(Weight){
 return evaluate(code,Weight.get(0).unwrap_or(1),input);
}
change frame(code:List<u32>,input:List<u32>,fail:Bool)->Result<List<u32>,String>
 reads(Weight,Count) writes(Count) emits(advanced){
 let n=Count.get(0).unwrap_or(0)+1;Count.put(0,n);emit advanced(n);
 let result=evaluate(code,Weight.get(0).unwrap_or(1),input);
 if fail{return Err("rollback");}return Ok(result);
}
'''


class FoldStateProjection(unittest.TestCase):
    def test_shared_body_plan_preserves_live_state_events_and_rollback(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root/'target/debug/ink')).resolve()
        with tempfile.TemporaryDirectory() as temporary:
            d = Path(temporary)
            def run(*args, success=True):
                result = subprocess.run(list(map(str, args)), capture_output=True, text=True, timeout=180)
                self.assertEqual(result.returncode == 0, success, result.stderr[-3000:])
                return result
            source, core_file = d/'source.ink', d/'core.json'
            source.write_text(SOURCE)
            run(compiler, 'emit-core', source, '-o', core_file)
            core = json.loads(core_file.read_bytes())
            sid = json.loads(run(compiler, 'check-core', core_file).stdout)['core_sha256']
            self.assertEqual([(r['original']['name'], r['field']) for r in candidates(core)],
                             [('evaluate', 'values')])
            self.assertEqual(candidates(core, 0), [])
            coupled = copy.deepcopy(core)
            step = next(f for f in coupled['program']['functions'] if f['name'] == 'step')
            step['body']['Let'][2] = {'Field': [{'Var': 'work'}, 'total']}
            self.assertEqual(candidates(coupled), [])
            shadowed = copy.deepcopy(core)
            function = next(f for f in shadowed['program']['functions'] if f['name'] == 'evaluate')
            body = function['body']['Let']
            body[3] = {'Let': [body[0], None, {'Num': 0}, body[3]]}
            self.assertEqual(candidates(shadowed), [])
            store = Store.publish(d/'knowledge', [])
            registry, _ = load(store=store)
            recipe = next(r for r in registry['recipes'] if r['id'] == 'fold-state-projection')
            proposals = list(execute(recipe, dict(core=core, source=sid, compiler=str(compiler),
                knowledge_root=str(store.root), knowledge_snapshot=store.snapshot_id, check_timeout=180)))
            self.assertEqual(len(proposals), 1, proposals)
            self.assertEqual(proposals[0]['status'], 'proposal', proposals)
            plan = dict(schema=1, semantics='ink-compiled-plan-v1', input_core_sha256=sid,
                        steps=proposals[0]['steps'])
            path = d/'plan.json'
            path.write_bytes(canonical(plan))
            checked = run(compiler, 'check-plan', core_file, path, '--core', '--target', 'javascript')
            selected = json.loads(checked.stdout)['state']['core']
            evaluate = next(f for f in selected['program']['functions'] if f['name'] == 'evaluate')
            self.assertNotIn('total', json.dumps(evaluate['body']))
            for name, options in [('baseline', []), ('selected', ['--plan', path])]:
                run(compiler, 'compile' if options else 'build', core_file, '--core', *options,
                    '--target', 'javascript', '-o', d/(name+'.mjs'))
            script = d/'verify.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import {createState as a} from './baseline.mjs';import {createState as b} from './selected.mjs';
const x=a(),y=b();let cases=0;
for(const weight of [0,1,0xffffffff]){
 assert.deepEqual(x.invoke('retune',[weight]),y.invoke('retune',[weight]));
 for(const code of [[],[0],[0,1,2,3,4,5,6,7],[0xffffffff,0,1]])
 for(const input of [[],[1],[0,0xffffffff,17]]){
  for(const [call,args] of [['serve',[code,input]],['frame',[code,input,false]],['frame',[code,input,true]]]){
   const before=await x.checkpoint();assert.deepEqual(x.invoke(call,args),y.invoke(call,args));
   assert.deepEqual(await x.checkpoint(),await y.checkpoint());
   if(call==='frame'&&args[2])assert.deepEqual(await x.checkpoint(),before);cases++;
  }
 }
}console.log(JSON.stringify({cases,status:'passed'}));''')
            result = run('node', script)
            self.assertEqual(json.loads(result.stdout)['cases'], 108)
            # Rehash a false output conclusion, preserving valid membership and
            # the original proof. Matching source syntax confers no authority.
            bad = copy.deepcopy(plan)
            packet = bad['steps'][1]['package']
            view = packet['knowledge']
            old = view['roots'][0]
            obj = copy.deepcopy(view['objects'][old])
            obj['payload']['to'] = dict(sort={'Value': {'List': 'U32'}}, node='Nil')
            forged = semantic_entry(dict(schema=1, semantics=obj['semantics'],
                dependencies=obj['dependencies'], **obj['payload']))
            fid = identity(forged)
            objects = {k: v for k, v in view['objects'].items() if k != old}
            objects[fid] = forged
            packet['knowledge'] = ProposalViews(store, objects, d/'forged').bundle([fid])
            packet['applications'][0]['law'] = fid
            wrong = d/'wrong.json'
            wrong.write_bytes(canonical(bad))
            run(compiler, 'check-plan', core_file, wrong, '--core', success=False)
            # A well-typed, independently re-emitted alternative step has an
            # exact new source image. Its failed universal simulation must still
            # reject, independently of source hashes and training observations.
            extended = copy.deepcopy(core)
            row = candidates(core)[0]
            row['step']['body']['Let'][1] = 'U32'
            row['step']['body']['Let'][2] = {'Num': 99}
            extended['program']['functions'] += [row['step'], row['helper']]
            wrong_core, semantic = d/'wrong-core.json', d/'wrong-semantic.json'
            wrong_core.write_bytes(canonical(extended))
            run(compiler, 'check-core', wrong_core)
            run(compiler, 'emit-semantic', wrong_core, '--core', '-o', semantic)
            parent = Store(root/'knowledge/libraries/proofs/fold-projection')
            key = parent.names['fold/project']
            theorem = prove(extended, json.loads(semantic.read_bytes()), 'evaluate', row['helper']['name'], parent.object(key))
            false = semantic_entry(theorem)
            bank = Store.publish(d/'false-simulation', [*parent.bundle([key])['objects'].values(), false])
            wrong_view = d/'wrong-view.json'
            wrong_view.write_bytes(canonical(bank.bundle([identity(false)])))
            rejected = run(compiler, 'knowledge-check', wrong_core, wrong_view, success=False)
            self.assertIn('semantic normal forms differ', rejected.stderr)


if __name__ == '__main__':
    unittest.main()
