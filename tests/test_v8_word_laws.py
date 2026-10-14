"""V8-inspired proposals remain ordinary checked, source-bound Ink laws."""
import copy
import gzip
import json
import os
import random
import subprocess
import tempfile
import unittest
from pathlib import Path
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.v8_word_laws import templates, specialize
from producers.frozen_laws import read
from .test_word_facts import evaluate


class V8WordLaws(unittest.TestCase):
    def test_templates_preserve_wrapping_values_and_modular_counts(self):
        rng = random.Random(0x7838)
        rows = templates()
        self.assertEqual(len({r['name'] for r in rows}), len(rows))
        for row in rows:
            goal = row['goal']
            for i in range(100):
                values = {}
                for name, sort in goal['params'].items():
                    width = {'U32': 32, 'U64': 64, 'Bool': 1}[sort['Value']]
                    values[name] = ([0, 1, width-1, width, width+1, (1 << width)-1][i % 6]
                                    if i < 36 else rng.getrandbits(width)) & ((1 << width)-1)
                if all(evaluate(e['from'], values) == evaluate(e['to'], values) for e in goal['conditions']):
                    self.assertEqual(evaluate(goal['from'], values), evaluate(goal['to'], values), row['name'])

    def test_frozen_proofs_replay_and_missing_premises_or_bytes_reject(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root/'target/debug/ink')).resolve()
        rows = read(root/'knowledge/producers/data/v8-word-laws')
        goals = {r['name']: r['goal'] for r in templates()}
        self.assertGreaterEqual(len(rows), 50)
        self.assertEqual(len({r['name'] for r in rows}), len(rows))
        for row in rows:
            self.assertEqual({k:row['law'][k] for k in ('params','conditions','from','to')}, goals[row['name']])
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp); source = d/'source.ink'; core = d/'core.json'
            source.write_text('module independent_v8_replay;fn identity(x:u32)->u32{return x;}')
            def run(*args):
                return subprocess.run([str(compiler), *map(str,args)], capture_output=True, text=True, timeout=120)
            result = run('emit-core', source, '-o', core)
            self.assertEqual(result.returncode, 0, result.stderr)
            def check(laws, name):
                objects = [semantic_entry(law) for law in laws]
                st = Store.publish(d/name, objects)
                view = d/(name+'.json'); view.write_bytes(canonical(st.bundle([identity(o) for o in objects])))
                return run('knowledge-check', core, view)
            for i,row in enumerate(rows):
                result = check([row['law']], 'valid-'+str(i))
                self.assertEqual(result.returncode, 0, (row['name'],result.stderr))
            for name in ('u32/or_covers_mask','u64/bitfield_checks','u64/shift_right_count_mask'):
                original = next(r['law'] for r in rows if r['name']==name)
                bad = copy.deepcopy(original); bad['conditions']=[]; bad['proof']['BitVector']['hypotheses']=[]
                self.assertNotEqual(check([bad],name.replace('/','-')+'-premise').returncode,0)
            bad = copy.deepcopy(rows[0]['law']); bad['proof']['BitVector']['certificate']['steps']=[]
            self.assertNotEqual(check([bad],'proof').returncode,0)
            self.assertEqual(specialize({'functions':{}},{}),[])

    def test_discovery_uses_renamed_sites_and_actual_count_premise(self):
        from ink_planner.semantic_search import match
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        rows = read(root/'knowledge/producers/data/v8-word-laws')
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp)
            for kind,width in [('u32',32),('u64',64)]:
                law=next(row['law'] for row in rows if row['name']==kind+'/shift_right_count_mask')
                obj=semantic_entry(law); ident=identity(obj)
                st=Store.publish(d/kind,[obj])
                for mask in (0,(width-1)>>1,width-1,2*width-1,(1<<32)-1):
                    source=d/'source.ink';core=d/'core.json';semantic=d/'semantic.json'
                    source.write_text('module renamed_shift;fn payload(data:'+kind+',count:u32)->'+kind+
                                      '{return wrapping_shr(data,word_and(count,'+str(mask)+'));}')
                    def run(*args):
                        return subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=60)
                    for args in [('emit-core',source,'-o',core),('emit-semantic',core,'--core','-o',semantic)]:
                        result=run(*args);self.assertEqual(result.returncode,0,result.stderr)
                    subject=json.loads(semantic.read_bytes());arguments={}
                    self.assertTrue(match(law['from'],subject['functions']['payload'],law['params'],arguments))
                    self.assertIn('v8-word/'+kind+'/shift_right_count_mask',dict(specialize(subject,{})))
                    packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],
                        knowledge=st.bundle([ident]),applications=[dict(function='payload',path=[],law=ident,
                                                                      arguments=arguments,premises=['Normalize'])])
                    selection=d/'selection.json';selection.write_bytes(canonical(packet))
                    result=run('check-selection',core,selection)
                    valid = mask & (width-1) == width-1
                    self.assertEqual(result.returncode==0,valid,result.stderr)
                    if valid:
                        # Even correct proof bytes cannot authorize another input module.
                        packet['input_core_sha256']='0'*64;selection.write_bytes(canonical(packet))
                        self.assertNotEqual(run('check-selection',core,selection).returncode,0)


if __name__ == '__main__':
    unittest.main()
