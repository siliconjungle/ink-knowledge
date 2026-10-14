"""Verified-at-use interval hints under rotations, splits and invalidation."""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest


class IntervalCursor(unittest.TestCase):
    def test_stale_and_invalid_handles_preserve_lookup(self):
        root=Path(__file__).resolve().parents[2];compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'));rng=random.Random(68926)
        rows=[]
        for _ in range(150):
            ends=sorted(rng.sample(range(1,100000),rng.randrange(4,100)));entries=[]
            for i in range(0,len(ends)-1,2):entries.append(dict(start=ends[i],end=ends[i+1],value=i+1))
            rng.shuffle(entries);queries=[];expected=[]
            for _ in range(350):
                key=rng.choice([rng.randrange(100001),rng.choice(ends)]);hint=rng.randrange(len(entries)+5)
                queries.append(dict(key=str(key),hint=hint));expected.append(next((e['value']for e in entries if e['start']<=key<e['end']),0))
            rows.append(dict(entries=[{**e,'start':str(e['start']),'end':str(e['end'])}for e in entries],queries=queries,expected=expected))
        rows.append(dict(entries=[dict(start='18446744073709551615',end='0',value=7)],queries=[dict(key='18446744073709551615',hint=1),dict(key='0',hint=1)],expected=[7,0]))
        with tempfile.TemporaryDirectory()as temporary:
            d=Path(temporary)
            def run(*args):
                result=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=180);self.assertEqual(result.returncode,0,result.stderr[-3000:]);return result
            source=root/os.environ.get('INK_INTERVAL_SOURCE','examples/crdts/interval_cursor.ink');core=d/'core.json';run(compiler,'emit-core',source,'-o',core)
            args=d/'args.json';args.write_text('[]');self.assertEqual(json.loads(run(compiler,'run',core,'split_hint',args,'--core').stdout),[2,2,2])
            run(compiler,'build',source,'--target','javascript','-o',d/'compiled.mjs');(d/'cases.json').write_text(json.dumps(rows))
            script=d/'verify.mjs';script.write_text('''import assert from 'node:assert/strict';import fs from 'node:fs';import {functions} from './compiled.mjs';
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){
 const entries=row.entries.map(e=>({...e,start:BigInt(e.start),end:BigInt(e.end)})),queries=row.queries.map(q=>({...q,key:BigInt(q.key)}));
 assert.deepEqual(functions.values(entries,queries,true),row.expected);
 assert.deepEqual(functions.values(entries,queries,true),functions.values(entries,queries,false));
}
assert.deepEqual(functions.split_hint(),[2,2,2]);
''');run('node',script)


if __name__=='__main__':unittest.main()
