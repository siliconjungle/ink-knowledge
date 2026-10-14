"""Compressed causal walking versus an independent list/ancestor-set model."""
import copy
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest


class Oracle:
    def __init__(self):
        self.atoms=[]
        self.deletes=[]
        self.ancestors={}

    def closure(self,parents):
        result=set()
        for parent in parents:result.update(self.ancestors[parent])
        return result

    def visible(self,reached):
        deleted={target for owner,target in self.deletes if owner in reached}
        return [a for a in self.atoms if a['owner'] in reached and a['id'] not in deleted]

    def integrate(self,atom):
        positions={a['id']:i+1 for i,a in enumerate(self.atoms)}
        left=positions.get(atom['left'],0)
        right=positions.get(atom['right'],len(self.atoms)+1)
        i=left;destination=left;scanning=False
        while True:
            if not scanning:destination=i
            if i==len(self.atoms) or i+1==right:break
            other=self.atoms[i]
            ol=positions.get(other['left'],0)
            ore=positions.get(other['right'],len(self.atoms)+1)
            if ol<left or (ol==left and ore==right and atom['id']<other['id']):break
            if ol==left:scanning=ore<right
            i+=1
        self.atoms.insert(destination,atom)

    def apply(self,change,index):
        reached=self.closure(change['parents']);reached.add(index)
        position=change['position']
        for _ in range(change['remove']):
            self.deletes.append((index,self.visible(reached)[position]['id']))
        for offset,value in enumerate(change['text']):
            visible=self.visible(reached)
            left=visible[position+offset-1]['id'] if position+offset else 0
            raw=next((i+1 for i,a in enumerate(self.atoms) if a['id']==left),0)
            right=next((a['id'] for a in self.atoms[raw:] if a['owner'] in reached),0)
            self.integrate(dict(id=change['id']+change['remove']+offset,left=left,right=right,value=value,owner=index))
        self.ancestors[change['id']+change['remove']+len(change['text'])-1]=reached

    def result(self):
        deleted={target for _,target in self.deletes}
        return [a['value'] for a in self.atoms if a['id'] not in deleted]


def generated(seed=68919,count=400,maximum=42):
    rng=random.Random(seed);rows=[]
    for history in range(count):
        model=Oracle();changes=[];counters={}
        for index in range(1,rng.randrange(2,maximum)):
            ends=list(model.ancestors)
            parents=rng.sample(ends,rng.randrange(min(len(ends),3)+1))
            view=model.visible(model.closure(parents));position=rng.randrange(len(view)+1)
            remove=rng.randrange(min(8,len(view)-position)+1)
            text=[rng.choice([65,66,67,233,0,128578,1114111]) for _ in range(rng.randrange(1 if not remove else 0,13))]
            actor=rng.randrange(1,5);counter=counters.get(actor,0)+1
            counters[actor]=counter+remove+len(text)-1
            change=dict(id=(actor<<32)|counter,parents=parents,position=position,remove=remove,text=text)
            model.apply(change,index);changes.append(change)
        rows.append(dict(name=f'random-{history}',changes=changes,expected=model.result()))
    return rows


class SpanEventGraph(unittest.TestCase):
    def test_runs_splits_deletion_counts_branches_and_invalid_inputs(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
        source=root/os.environ.get('INK_SPAN_SOURCE','examples/crdts/span_graph.ink')
        rows=generated()
        # Exercise the 2^64 interval-end sentinel and same-actor branches
        # arriving in counter order different from their causal/topological order.
        for name,changes in [
            ('maximum-identity',[dict(id=18446744073709551615,parents=[],position=0,remove=0,text=[1114111]),dict(id=4294967297,parents=[],position=0,remove=0,text=[0])]),
            ('same-actor-reverse',[dict(id=4294967396,parents=[],position=0,remove=0,text=[67,68]),dict(id=4294967297,parents=[],position=0,remove=0,text=[65,66])]),
            ('duplicate-frontier',[dict(id=4294967297,parents=[],position=0,remove=0,text=[65,66,67]),dict(id=8589934593,parents=[4294967299,4294967299],position=1,remove=1,text=[90])]),
        ]:
            model=Oracle()
            for index,change in enumerate(changes,1):model.apply(change,index)
            rows.append(dict(name=name,changes=changes,expected=model.result()))
        # Interior frontiers must retain the scalar semantics through fallback.
        base=dict(id=4294967297,parents=[],position=0,remove=0,text=[65,66,67,68])
        rows.append(dict(name='interior-parent',changes=[base,dict(id=8589934593,parents=[4294967298],position=2,remove=0,text=[90])]))
        for name,change in [('overlap',dict(id=4294967299,parents=[4294967300],position=0,remove=0,text=[90])),
                            ('bad-position',dict(id=8589934593,parents=[4294967300],position=5,remove=0,text=[90])),
                            ('bad-delete',dict(id=8589934593,parents=[4294967300],position=2,remove=3,text=[])),
                            ('surrogate',dict(id=8589934593,parents=[4294967300],position=0,remove=0,text=[55296])),
                            ('missing-parent',dict(id=8589934593,parents=[17],position=0,remove=0,text=[90]))]:
            rows.append(dict(name=name,changes=[copy.deepcopy(base),change]))
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            def run(*args,timeout=180):
                result=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=timeout)
                self.assertEqual(result.returncode,0,result.stderr[-4000:]);return result
            core=directory/'core.json';run(compiler,'emit-core',source,'-o',core)
            for row in generated(seed=68920,count=8,maximum=7)+rows[-6:]:
                args=directory/'args.json';args.write_text(json.dumps([row['changes']]))
                actual=json.loads(run(compiler,'run',core,'materialize',args,'--core').stdout)
                scalar=json.loads(run(compiler,'run',core,'scalar',args,'--core').stdout)
                self.assertEqual(actual,scalar,row['name'])
                if 'expected' in row:self.assertEqual(actual,{'Ok':row['expected']},row['name'])
            run(compiler,'build',source,'--target','javascript','-o',directory/'compiled.mjs')
            # JavaScript JSON numbers cannot transport every u64 identity exactly.
            transported=[{**row,'changes':[{**c,'id':str(c['id']),'parents':list(map(str,c['parents']))}for c in row['changes']]}for row in rows]
            (directory/'cases.json').write_text(json.dumps(transported))
            script=directory/'verify.mjs'
            script.write_text('''import assert from 'node:assert/strict';
import fs from 'node:fs';
import {functions} from './compiled.mjs';
for(const row of JSON.parse(fs.readFileSync(new URL('./cases.json',import.meta.url)))){
 const changes=row.changes.map(c=>({...c,id:BigInt(c.id),parents:c.parents.map(BigInt)}));
 const actual=functions.materialize(changes), scalar=functions.scalar(changes);
 assert.deepEqual(actual,scalar,row.name+' '+JSON.stringify(row.changes));
 if(row.expected) {
  assert.deepEqual(actual,{Ok:row.expected},row.name+' independent oracle');
  assert.deepEqual(functions.walked(changes),actual,row.name+' forced compressed path');
 }
}
const base=4294967297n,other=8589934593n;
const changes=[{id:base,parents:[],position:0,remove:0,text:Array(100000).fill(65)},
 {id:other,parents:[],position:0,remove:0,text:Array(100000).fill(66)}];
assert.deepEqual(functions.metrics(changes),[3,3,200000,2,2]);
assert.equal(functions.materialize(changes).Ok.length,200000);
''')
            run('node',script)


if __name__=='__main__':unittest.main()
