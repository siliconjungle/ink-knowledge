"""Bulk gap writes preserve scalar insertion under movement and growth."""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest


class BulkGap(unittest.TestCase):
    def test_growth_movement_zero_chunks_and_malformed_fallback(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(68925)
        rows=[]
        for history in range(120):
            edits=[];values=[]
            for _ in range(rng.randrange(1,70)):
                position=rng.randrange(len(values)+12);remove=rng.randrange(14)
                text=[rng.randrange(4294967296)for _ in range(rng.choice([0,1,2,7,31,32,33,65,257]))]
                at=min(position,len(values));values[at:at+remove]=text
                edits.append(dict(position=position,remove=remove,text=text))
            rows.append(dict(edits=edits,expected=values))
        rows.insert(0,dict(edits=[],expected=[]))
        with tempfile.TemporaryDirectory()as temporary:
            directory=Path(temporary)
            def run(*args):
                result=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=180)
                self.assertEqual(result.returncode,0,result.stderr[-3000:]);return result
            source=root/os.environ.get('INK_BULK_GAP_SOURCE','examples/crdts/bulk_gap.ink');core=directory/'core.json';run(compiler,'emit-core',source,'-o',core)
            for row in rows[:6]:
                # The reference evaluator has explicit copy/fuel limits; use
                # short histories while native JS executes the complete cases.
                edits=row['edits'][:4];args=directory/'args.json'
                args.write_text(json.dumps([edits,True]));actual=json.loads(run(compiler,'run',core,'run',args,'--core').stdout)
                args.write_text(json.dumps([edits,False]));scalar=json.loads(run(compiler,'run',core,'run',args,'--core').stdout)
                self.assertEqual(actual,scalar)
            run(compiler,'build',source,'--target','javascript','-o',directory/'compiled.mjs')
            (directory/'cases.json').write_text(json.dumps(rows));script=directory/'verify.mjs'
            script.write_text('''import assert from 'node:assert/strict';import fs from 'node:fs';import {functions} from './compiled.mjs';
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){
 assert.deepEqual(functions.run(row.edits,true),row.expected);
 assert.deepEqual(functions.run(row.edits,true),functions.run(row.edits,false));
}
for(const [start,end]of [[3,1],[0,9],[7,9],[0,0]]){
 assert.deepEqual(functions.malformed([1,2,3],start,end,[7,8],true),functions.malformed([1,2,3],start,end,[7,8],false));
}
const long=Array(200000).fill(65);assert.deepEqual(functions.run([{position:0,remove:0,text:long},{position:100000,remove:3,text:[7,8]}],true),long.slice(0,100000).concat([7,8],long.slice(100003)));
''');run('node',script)


if __name__=='__main__':unittest.main()
