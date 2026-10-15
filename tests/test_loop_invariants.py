"""Strict callback hoisting uses ordinary source binding and normalization."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.definition_context28 import bind
from producers.loop_invariants import specialize

SOURCE = Path(__file__).parent/'fixtures/loop-invariants/source.ink'


def prepare(directory, compiler):
    d = Path(directory);d.mkdir(parents=True, exist_ok=True)
    def run(*args):
        result=subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=60)
        if result.returncode:raise AssertionError(result.stderr)
        return result
    run('emit-core',SOURCE,'-o',d/'core.json')
    run('emit-semantic',d/'core.json','--core','-o',d/'semantic.json')
    model=json.loads((d/'core.json').read_bytes());subject=json.loads((d/'semantic.json').read_bytes())
    rows=specialize(subject,model);selected={}
    for name,raw in rows:
        function=name.split('/')[1]
        proposal=bind(raw,model,subject);obj=semantic_entry(proposal)
        store=Store.publish(d/'knowledge',[obj])
        packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=store.bundle([identity(obj)]),
                    applications=[dict(function=function,path=[],law=identity(obj),arguments={n:dict(sort=s,node={'Free':n})for n,s in proposal['params'].items()},premises=[])])
        p=d/'candidate.json';p.write_bytes(canonical(packet));run('check-selection',d/'core.json',p)
        selected.setdefault(function,packet)
    entries={};applications=[]
    for packet in selected.values():
        entries.update(packet['knowledge']['objects']);applications+=packet['applications']
    packet=copy.deepcopy(next(iter(selected.values())))
    store=Store.publish(d/'combined',entries.values())
    packet['knowledge']=store.bundle(sorted(entries))
    packet['applications']=applications
    (d/'selection.json').write_bytes(canonical(packet));run('check-selection',d/'core.json',d/'selection.json')
    return model,subject,rows,packet


class LoopInvariants(unittest.TestCase):
    def test_checked_candidates_and_strict_regions(self):
        compiler=Path(os.environ['INK_COMPILER']).resolve()
        with tempfile.TemporaryDirectory()as tmp:
            d=Path(tmp);_,subject,rows,packet=prepare(d,compiler)
            functions={a['function']for a in packet['applications']}
            self.assertEqual(functions,{'mapped','filtered','folded','right','nested','floats','whole_choice','wide','signed','booleans','captured'})
            for name,raw in rows:
                if name.split('/')[1] not in ('nested','captured'):
                    self.assertEqual(raw['to']['node']['Op'][0],'call:choose')
                    self.assertEqual(raw['to']['node']['Op'][1][2],raw['from'])
            for name in functions:
                for xs,ys in [([],[]),([],[1,2,3]),([0,1,4294967295],[]),([0,7,9],[4294967295,3])]:
                    if name=='signed':
                        xs=[x if x<2147483648 else x-4294967296 for x in xs]
                        ys=[x if x<2147483648 else x-4294967296 for x in ys]
                    args=[xs,ys]+([7]if name in ('folded','right','nested','floats')else [False]if name=='whole_choice'else [])
                    p=d/'input.json';p.write_text(json.dumps(args))
                    def run(extra):
                        return subprocess.run([str(compiler),'run',str(d/'core.json'),name,str(p),'--core',*extra],check=True,capture_output=True,text=True,timeout=60).stdout
                    self.assertEqual(json.loads(run([])),json.loads(run(['--selection',str(d/'selection.json')])))
            forged=copy.deepcopy(rows[0][1]);forged['to']=dict(sort=forged['from']['sort'],node='Nil')
            model=json.loads((d/'core.json').read_bytes());obj=semantic_entry(bind(forged,model,subject))
            store=Store.publish(d/'bad',[obj]);p=d/'bad.json';p.write_bytes(canonical(store.bundle([identity(obj)])))
            bad=subprocess.run([str(compiler),'knowledge-check',str(d/'core.json'),str(p)],capture_output=True,text=True,timeout=60)
            self.assertNotEqual(bad.returncode,0)


if __name__=='__main__':
    import sys
    if len(sys.argv)==2:
        prepare(sys.argv[1],Path(os.environ['INK_COMPILER']).resolve())
    else:
        unittest.main()
