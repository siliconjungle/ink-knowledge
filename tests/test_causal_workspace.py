"""Repeated DAG queries versus independent ancestor sets and the old walker."""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest


def ancestors(parents):
    sets=[set()]
    for index,row in enumerate(parents,1):
        if any(p<=0 or p>=index for p in row):return None
        reached={index}
        for parent in row:reached.update(sets[parent])
        sets.append(reached)
    return sets


def expected(parents,query):
    sets=ancestors(parents)
    if sets is None or any(p<=0 or p>=len(sets)for p in query['left']+query['right']):
        return dict(valid=False)
    def closure(frontier):return set().union(*(sets[p]for p in frontier))
    left=closure(query['left']);right=closure(query['right'])
    return dict(valid=True,removed=sorted(left-right),added=sorted(right-left))


class CausalWorkspace(unittest.TestCase):
    def test_repeated_queries_recycling_rollover_and_append(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
        source=root/os.environ.get('INK_CAUSAL_SOURCE','examples/crdts/causal_workspace.ink');rng=random.Random(821018)
        rows=[]
        graphs=[[],[[]],[[],[1],[1],[2,3],[4]],[[],[1,1],[2]],[[0]],[[1]],[[],[2]]]
        for _ in range(120):
            graphs.append([rng.choices(range(1,i),k=rng.randrange(min(i,4)))if i>1 else[] for i in range(1,rng.randrange(2,45))])
        for parents in graphs:
            n=len(parents)
            queries=[dict(left=[],right=[]),dict(left=[0],right=[]),dict(left=[],right=[n+1])]
            for _ in range(30):
                queries.append(dict(left=rng.choices(range(1,n+1),k=rng.randrange(4))if n else[],right=rng.choices(range(1,n+1),k=rng.randrange(4))if n else[]))
            rows.append(dict(parents=parents,queries=queries,expected=[expected(parents,q)for q in queries],progressive=[expected(parents[:i],dict(left=[i-1]if i>1 else[],right=[i]))for i in range(1,n+1)]))
        with tempfile.TemporaryDirectory()as temporary:
            directory=Path(temporary)
            def run(*args):
                result=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=180)
                self.assertEqual(result.returncode,0,result.stderr[-4000:]);return result
            core=directory/'core.json';run(compiler,'emit-core',source,'-o',core)
            for row in rows[:7]:
                args=directory/'args.json';args.write_text(json.dumps([row['parents'],row['queries'][:5],False]))
                normal=json.loads(run(compiler,'run',core,'queries',args,'--core').stdout)
                args.write_text(json.dumps([row['parents'],row['queries'][:5],True]))
                wrapped=json.loads(run(compiler,'run',core,'queries',args,'--core').stdout)
                args.write_text(json.dumps([row['parents'],row['queries'][:5]]))
                scalar=json.loads(run(compiler,'run',core,'scalar',args,'--core').stdout)
                self.assertEqual(normal,wrapped);self.assertEqual(normal,scalar)
            run(compiler,'build',source,'--target','javascript','-o',directory/'compiled.mjs')
            (directory/'cases.json').write_text(json.dumps(rows))
            script=directory/'verify.mjs';script.write_text('''import assert from 'node:assert/strict';
import fs from 'node:fs';import {functions} from './compiled.mjs';
const expanded=ranges=>ranges.flatMap(r=>Array.from({length:r.end-r.start},(_,i)=>r.start+i)).sort((a,b)=>a-b);
function check(got,want){assert.equal(got.valid,want.valid);if(want.valid){assert.deepEqual(expanded(got.removed),want.removed);assert.deepEqual(expanded(got.added),want.added);}}
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){
 const actual=functions.queries(row.parents,row.queries,false);
 assert.deepEqual(actual,functions.queries(row.parents,row.queries,true),'rollover');
 assert.deepEqual(actual,functions.scalar(row.parents,row.queries),'scalar range order');
 actual.forEach((answer,i)=>check(answer,row.expected[i]));
 const progressive=functions.progressive(row.parents,false);
 assert.deepEqual(progressive,functions.progressive(row.parents,true),'append after queries');
 progressive.forEach((answer,i)=>check(answer,row.progressive[i]));
}
const n=10000,chain=Array.from({length:n},(_,i)=>i===0?[]:[i]);
assert.deepEqual(functions.queries(chain,[{left:[n],right:[n-10]},{left:[n-20],right:[n]}],false),[
 {removed:[{start:n-9,end:n+1}],added:[],valid:true},
 {removed:[],added:[{start:n-19,end:n+1}],valid:true}]);
''');run('node',script)


if __name__=='__main__':unittest.main()
