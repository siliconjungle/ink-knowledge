"""Exact scalar sharing stays capture safe and independently checked."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.definition_context28 import bind
from producers.common_subexpressions import specialize


class CommonSubexpressions(unittest.TestCase):
    def test_source_capture_identity_values_and_forged_sharing(self):
        compiler=Path(os.environ['INK_COMPILER']).resolve()
        source='''module sharing_checks;
fn scalar(x:u64)->u64{return (x*7)+(x*7);}
fn sum_twice(xs:List<u32>)->u32{return foldl(xs,0,fn(x)=>fn(a)=>a+x)+foldl(xs,0,fn(x)=>fn(a)=>a+x);}
fn nested(xs:List<u32>,outer:u32)->List<u32>{return xs.map(fn(x)=>(x+outer)*(x+outer));}
fn shadow(xs:List<u32>,outer:u32)->List<u32>{return xs.map(fn(x)=>(x+outer)+foldl(xs,0,fn(x)=>fn(y)=>(x+y)*(x+y)));}
fn floats(x:f32)->f32{return (x*2.0)+(x*2.0);}
fn separate(xs:List<u32>)->List<u32>{return xs.map(fn(x)=>x+1).concat(xs.map(fn(x)=>x+1));}
'''
        with tempfile.TemporaryDirectory()as tmp:
            d=Path(tmp);p=d/'source.ink';core=d/'core.json';semantic=d/'semantic.json';p.write_text(source)
            def run(*args):
                r=subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=60)
                self.assertEqual(r.returncode,0,r.stderr);return r
            run('emit-core',p,'-o',core);run('emit-semantic',core,'--core','-o',semantic)
            model=json.loads(core.read_bytes());subject=json.loads(semantic.read_bytes());rows=specialize(subject,model)
            self.assertTrue(rows)
            self.assertFalse(any('/separate/' in n for n,_ in rows))
            for number,(name,raw) in enumerate(rows):
                proposal=bind(raw,model,subject);obj=semantic_entry(proposal);store=Store.publish(d/('knowledge'+str(number)),[obj])
                # One whole-function law per packet, independently bound to source.
                function=name.split('/')[1]
                packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=store.bundle([identity(obj)]),
                            applications=[dict(function=function,path=[],law=identity(obj),arguments={n:dict(sort=s,node={'Free':n}) for n,s in proposal['params'].items()},premises=[])])
                selected=d/'selection.json';selected.write_bytes(canonical(packet));run('check-selection',core,selected)
                cases={'scalar':[[0],[18446744073709551615]],'sum_twice':[[[]],[[0,4294967295,7]]],
                       'nested':[[[1,7,4294967295],4294967295]],'shadow':[[[1,7,4294967295],4]],'floats':[[0.0],[-0.0],[1.25],[-3.5]]}
                for args in cases[function]:
                    inp=d/'input.json';inp.write_text(json.dumps(args))
                    a=run('run',core,function,inp,'--core');b=run('run',core,function,inp,'--core','--selection',selected)
                    self.assertEqual(json.loads(a.stdout),json.loads(b.stdout),name)
            raw=copy.deepcopy(rows[0][1]);raw['to']=dict(sort=raw['from']['sort'],node={'Word':17})
            proposal=bind(raw,model,subject);obj=semantic_entry(proposal);store=Store.publish(d/'bad',[obj]);view=d/'bad.json';view.write_bytes(canonical(store.bundle([identity(obj)])))
            bad=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],capture_output=True,text=True,timeout=60)
            self.assertNotEqual(bad.returncode,0)

if __name__=='__main__':unittest.main()
