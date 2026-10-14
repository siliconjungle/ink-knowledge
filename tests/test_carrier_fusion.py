"""Generic filter/fold proposals require ordinary induction and exact-source replay."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity, semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_knowledge.law_templates import generate
from ink_planner.semantic_search import SelectionChecker, match
from producers.pipeline_templates import templates


SOURCE = '''module GeneralFilterFold;
record Row { key:u32, keep:Bool, }
fn checksum(xs:List<Row>,seed:u32,bias:u32)->u32 {
 return foldr(xs.filter(fn(r)=>r.keep),seed,fn(r)=>fn(a)=>a*33+r.key+bias);
}
fn best(xs:List<Row>,initial:Row)->Row {
 return foldr(xs.filter(fn(r)=>r.keep),initial,fn(r)=>fn(a)=>choose(r.key>a.key,r,a));
}
fn decision(xs:List<f32>,threshold:f32,initial:Bool)->Bool {
 return foldr(xs.filter(fn(x)=>x>threshold),initial,fn(x)=>fn(a)=>(x<10.0)||a);
}
fn collisions(xs:List<u32>,fusion_sequence:u32,fusion_head:u32,fusion_tail:u32)->u32 {
 return foldr(xs.filter(fn(x)=>x>fusion_sequence),fusion_head,fn(x)=>fn(a)=>x-a+fusion_tail);
}
'''


class FilterFold(unittest.TestCase):
    def test_arbitrary_carriers_accumulators_captures_and_tampering(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);source=d/'source.ink';core=d/'core.json';subject=d/'subject.json'
            source.write_text(SOURCE)
            def run(*args):
                return subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=60)
            for command in [('emit-core',source,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
                result=run(*command);self.assertEqual(result.returncode,0,result.stderr)
            subjects=json.loads(subject.read_bytes())
            core_value=json.loads(core.read_bytes())
            template=next(row['object'] for row in templates() if row['name']=='foldr-filter')
            library=Store.publish(d/'templates',[template]);library.refresh_index()
            generated,receipts=generate(library,subjects,core_value)
            self.assertEqual(receipts[0]['instances'],4)
            objects=list(generated.values());ids=list(generated)
            rows=[obj['payload'] for obj in objects]
            store=Store.publish(d/'valid',objects)
            view=d/'view.json';view.write_bytes(canonical(store.bundle(ids)))
            checked=run('knowledge-check',core,view)
            self.assertEqual(checked.returncode,0,checked.stderr)
            checker=SelectionChecker(compiler,core,ProposalViews(store,dict(zip(ids,objects)),d/'views'),d)
            try:
                applications=[]
                for name,term in subjects['functions'].items():
                    applicable=[]
                    for ident,law in zip(ids,rows):
                        args={}
                        if match(law['from'],term,law['params'],args):
                            applicable.append(dict(function=name,path=[],law=ident,arguments=args,premises=[]))
                    self.assertEqual(len(applicable),1,name)
                    applications.extend(applicable)
                self.assertTrue(checker.check(applications),checker.last_error)
            finally:checker.close()
            # Retaining every element instead of applying the predicate is not equal.
            bad=copy.deepcopy(rows[0])
            bad.update(semantics=objects[0]['semantics'],dependencies=objects[0]['dependencies'])
            body=bad['to']['node']['Op'][1][2]['node']['Lambda']['node']['Lambda']
            self.assertEqual(body['node']['Op'][0],'call:choose')
            body.update(copy.deepcopy(body['node']['Op'][1][1]))
            obj=semantic_entry(bad);forged=Store.publish(d/'forged',[obj])
            view.write_bytes(canonical(forged.bundle([identity(obj)])))
            rejected=run('knowledge-check',core,view)
            self.assertNotEqual(rejected.returncode,0)


if __name__=='__main__':unittest.main()
