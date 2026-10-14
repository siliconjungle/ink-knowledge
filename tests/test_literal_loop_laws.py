"""Literal expansions reuse fixed semantics across carriers and lexical scopes."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_planner.semantic_search import positions,match
from producers.literal_loop_laws import specialize
from producers.definition_context28 import bind


class LiteralLoopLaws(unittest.TestCase):
    def test_checked_source_values_records_lists_captures_and_expansion_budget(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        source='''module literal_loop_checks;
record Batch{value:u32,items:List<u32>,}
fn scalar(seed:u32,extra:u32)->u32{return repeat(4,seed,fn(i)=>fn(a)=>a+extra+i);}
fn wide(seed:u64)->u64{return repeat(8,seed,fn(i)=>fn(a)=>a+word_widen_u32_to_u64(i));}
fn pack_list(seed:List<u32>)->List<u32>{return repeat(2,seed,fn(i)=>fn(a)=>a.concat([i]));}
fn pack_record(seed:Batch,extra:u32)->Batch{return repeat(4,seed,fn(i)=>fn(a)=>Batch{value:a.value+extra+i,items:a.items.concat([i])});}
fn nested(xs:List<u32>,seed:u32)->List<u32>{return xs.map(fn(extra)=>repeat(2,seed,fn(i)=>fn(a)=>a+extra+i));}
fn large(seed:u32)->u32{return repeat(9,seed,fn(i)=>fn(a)=>a+i);}
'''
        with tempfile.TemporaryDirectory()as tmp:
            d=Path(tmp);path=d/'source.ink';core=d/'core.json';semantic=d/'semantic.json'
            path.write_text(source)
            def run(*args):
                result=subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=60)
                self.assertEqual(result.returncode,0,result.stderr)
                return result
            run('emit-core',path,'-o',core);run('emit-semantic',core,'--core','-o',semantic)
            model=json.loads(core.read_bytes());subject=json.loads(semantic.read_bytes())
            rows=specialize(subject,model)
            self.assertEqual(len(rows),5)  # U32/4, U64/8, List/2, record/4, U32/2.
            # U32/2 is distinct from the List/2 carrier, even with equal counts.
            kinds={(json.dumps(law['from']['sort'],sort_keys=True),law['from']['node']['Op'][1][0]['node']['Nat']) for _,law in rows}
            self.assertIn((json.dumps({'Value':'U32'},sort_keys=True),2),kinds)
            applications=[];objects=[]
            for _,raw in rows:
                law=bind(raw,model,subject);obj=semantic_entry(law);objects.append(obj)
                for name,body in subject['functions'].items():
                    for site,t in positions(body):
                        arguments={}
                        if match(law['from'],t,law['params'],arguments):
                            applications.append(dict(function=name,path=list(site),law=identity(obj),arguments=arguments,premises=[]))
            self.assertEqual({a['function']for a in applications},{'scalar','wide','pack_list','pack_record','nested'})
            store=Store.publish(d/'knowledge',objects)
            packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],
                        knowledge=store.bundle([identity(o)for o in objects]),applications=applications)
            selected=d/'selected.json';selected.write_bytes(canonical(packet));run('check-selection',core,selected)
            for name,args in [('scalar',[4294967295,7]),('wide',[18446744073709551615]),('pack_list',[[7,8]]),
                              ('pack_record',[{'value':4294967295,'items':[9]},3]),('nested',[[1,9,4294967295],4])]:
                inputs=d/'inputs.json';inputs.write_text(json.dumps(args))
                actual=run('run',core,name,inputs,'--core')
                changed=run('run',core,name,inputs,'--core','--selection',selected)
                self.assertEqual(json.loads(actual.stdout),json.loads(changed.stdout),name)
            # A rehashed proof object with one wrong iteration index must fail.
            raw=copy.deepcopy(next(law for _,law in rows if law['from']['node']['Op'][1][0]['node']['Nat']==4 and law['from']['sort']=={'Value':'U32'}))
            raw['to']['node']['Op'][1][0]['node']['Op'][1][1]['node']['Word']=99
            obj=semantic_entry(raw);bad=Store.publish(d/'bad',[obj]);view=d/'bad.json'
            view.write_bytes(canonical(bad.bundle([identity(obj)])))
            result=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],capture_output=True,text=True,timeout=60)
            self.assertNotEqual(result.returncode,0)


if __name__=='__main__':
    unittest.main()
