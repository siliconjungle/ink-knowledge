"""Dense membership critical cuts against the map implementation and reachability."""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest


def expected(parents):
    ancestors=[set()]
    for index,row in enumerate(parents,1):
        if any(parent<=0 or parent>=index for parent in row):return []
        reached={index}
        for parent in row:reached.update(ancestors[parent])
        ancestors.append(reached)
    return [True]+[
        ancestors[cut]==set(range(1,cut+1))
        and all(cut in ancestors[later] for later in range(cut+1,len(ancestors)))
        for cut in range(1,len(ancestors))
    ]


class DenseCausalCuts(unittest.TestCase):
    def test_late_branches_duplicate_parents_and_random_dags(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
        source=root/'examples/crdts/dense_causal_cuts.ink'
        rng=random.Random(821014)
        inputs=[[],[[]],[[],[1],[1],[2,3],[4]],[[],[1],[1]],
                [[],[1,1],[2]],[[] for _ in range(9)],[[0]],[[1]],[[],[2]]]
        for _ in range(500):
            graph=[]
            for index in range(1,rng.randrange(2,42)):
                graph.append(rng.sample(range(1,index),rng.randrange(min(index,4))))
            inputs.append(graph)
        rows=[dict(parents=graph,expected=expected(graph))for graph in inputs]
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            def run(*args):
                result=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=120)
                self.assertEqual(result.returncode,0,result.stderr[-3000:])
                return result
            core=directory/'core.json';run(compiler,'emit-core',source,'-o',core)
            # The independent Ink evaluator and native JS must agree with the
            # graph-set oracle. Include valid and malformed dependency cases.
            for row in rows[:15]:
                args=directory/'args.json';args.write_text(json.dumps([row['parents']]))
                result=json.loads(run(compiler,'run',core,'boundaries',args,'--core').stdout)
                self.assertEqual(result,row['expected'])
            run(compiler,'build',source,'--target','javascript','-o',directory/'compiled.mjs')
            (directory/'cases.json').write_text(json.dumps(rows))
            script=directory/'verify.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import fs from 'node:fs';
import {functions} from './compiled.mjs';
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){
 assert.deepEqual(functions.boundaries(row.parents),row.expected,JSON.stringify(row.parents));
 assert.deepEqual(functions.boundaries(row.parents),functions.original(row.parents));
}
const n=10000;
assert.deepEqual(functions.boundaries(Array.from({length:n},(_,i)=>i===0?[]:[i])),Array(n+1).fill(true));
''')
            run('node',script)


if __name__=='__main__':unittest.main()
