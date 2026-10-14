"""Catalogue discovery, source-bound equality and literal target execution."""
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
from producers.projected_arguments import candidates
from producers.semantic_laws import word


SOURCE = '''module observation_arguments;
record Detail{bias:u32,}
record Packet{items:List<u32>,detail:Detail,padding:List<u64>,}
fn extent(data:Packet,bonus:u32)->u32{
 let size=length(data.items);
 return size+data.detail.bias+bonus;
}
fn caller(data:Packet,bonus:u32)->u32{return extent(data,bonus);}
fn twice(data:Packet)->u32{return extent(data,1)+extent(data,2);}
fn contents(data:Packet)->List<u32>{return data.items;}
fn captured(data:Packet)->u32{
 return foldl(data.items,0,fn(x)=>fn(acc)=>acc+x+data.detail.bias);
}
fn shadowed(data:Packet)->u32{
 let size=length(data.items);
 let observed_0:u32=3;
 return size+data.detail.bias+observed_0;
}
'''


class ProjectedArguments(unittest.TestCase):
    def test_catalogue_proof_execution_and_forged_equality(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root/'target/debug/ink'))
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            source = directory/'source.ink'; source.write_text(SOURCE)

            def run(*arguments, success=True):
                result = subprocess.run(list(map(str, arguments)), capture_output=True,
                                        text=True, timeout=120)
                if success: self.assertEqual(result.returncode, 0, result.stderr[-3000:])
                else: self.assertNotEqual(result.returncode, 0)
                return result

            corefile = directory/'core.json'
            run(compiler, 'emit-core', source, '-o', corefile)
            core = json.loads(corefile.read_text())
            source_id = json.loads(run(compiler, 'check-core', corefile).stdout)['core_sha256']
            rows = candidates(core)
            self.assertEqual({row['original']['name'] for row in rows}, {'extent'})
            self.assertEqual(candidates(core, 0), [])
            store = Store.publish(directory/'knowledge', [])
            registry, _ = load(store=store)
            recipe = next(r for r in registry['recipes'] if r['id']=='scalar-observation-arguments')
            proposals = list(execute(recipe, dict(core=core, source=source_id,
                compiler=str(compiler.resolve()), knowledge_root=str(store.root),
                knowledge_snapshot=store.snapshot_id, check_timeout=120)))
            self.assertEqual(len(proposals), 1, proposals)
            self.assertEqual(proposals[0]['status'], 'proposal', proposals)
            package = dict(schema=1, semantics='ink-compiled-plan-v1',
                           input_core_sha256=source_id, steps=proposals[0]['steps'])
            plan = directory/'plan.json'; plan.write_bytes(canonical(package))
            run(compiler, 'check-plan', corefile, plan, '--core', '--target', 'javascript')
            selected = directory/'selected.mjs'
            baseline = directory/'baseline.mjs'
            run(compiler, 'emit-plan', corefile, plan, '--core',
                '--target', 'javascript', '-o', selected)
            run(compiler, 'build', corefile, '--core', '--target', 'javascript', '-o', baseline)
            script = directory/'verify.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import {functions as selected} from './selected.mjs';
import {functions as baseline} from './baseline.mjs';
for(const bias of [0,1,0xffffffff])for(const items of [[],[7],[0xffffffff,2,3]]){
 const data={items,detail:{bias},padding:[9007199254740993n]};
 for(const bonus of [0,1,0xffffffff]){
  const expected=(items.length+bias+bonus)>>>0;
  assert.equal(selected.caller(data,bonus),expected);
  assert.equal(selected.caller(data,bonus),baseline.caller(data,bonus));
 }
 assert.equal(selected.twice(data),((items.length+bias+1)+(items.length+bias+2))>>>0);
 assert.deepEqual(selected.contents(data),baseline.contents(data));
 assert.equal(selected.captured(data),baseline.captured(data));
 assert.equal(selected.shadowed(data),baseline.shadowed(data));
}
''')
            run('node', script)

            # Recompute transport hashes for a false equality. Membership and
            # a familiar producer name must not grant rewrite authority.
            forged = copy.deepcopy(package)
            rewrite = forged['steps'][1]['package']
            old_id = rewrite['knowledge']['roots'][0]
            obj = copy.deepcopy(rewrite['knowledge']['objects'][old_id])
            obj['payload']['to'] = word('U32', 0)
            obj = semantic_entry(dict(obj['payload'], schema=1,
                semantics=obj['semantics'], dependencies=obj['dependencies']))
            new_id = identity(obj)
            rewrite['knowledge'] = ProposalViews(store, {new_id:obj}, directory/'forged').bundle([new_id])
            for application in rewrite['applications']: application['law'] = new_id
            badfile = directory/'forged.json'; badfile.write_bytes(canonical(forged))
            result = run(compiler, 'check-plan', corefile, badfile, '--core',
                         '--target', 'javascript', success=False)
            self.assertIn('semantic normal forms differ', result.stderr.lower())
            self.assertEqual(Store(store.root).snapshot_id, store.snapshot_id)


if __name__ == '__main__':
    unittest.main()
