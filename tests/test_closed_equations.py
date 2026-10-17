"""Closed evaluation proposes modular equations, never an admission verdict."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical, identity
from ink_knowledge.store import entry, operations
from producers.action_replacement import MATH, call, cons, var
from producers.closed_equations import ClosedEquations
from producers.fold_chunks import FoldChunks

ROOT = Path(__file__).resolve().parents[2]
INK = Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()


class ClosedEvaluation(unittest.TestCase):
    def test_fixed_step_congruence_leaves_the_remaining_traversal_unevaluated(self):
        fixture=json.loads((Path(__file__).parent/'fixtures/closed-traversal-congruence.json').read_bytes())
        chunks=FoldChunks(fixture['objects'],[]);equation=fixture['equation']
        proof=ClosedEquations(chunks).conversion(equation['from'],equation['to'])
        self.assertIn('Call',proof)
        theorem=chunks.theorem([],equation['from'],equation['to'],proof)
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary);source=folder/'source.ink';source.write_text('module congruence;fn f(x:u32)->u32{return x;}')
            core=folder/'core.json';result=subprocess.run([INK,'emit-core',source,'-o',core],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr)
            store=Store.publish(folder/'proof',list(chunks.objects.values()))
            view=folder/'view.json';view.write_bytes(canonical(store.bundle([theorem])))
            result=subprocess.run([INK,'knowledge-check',core,view],capture_output=True,text=True,timeout=180)
            self.assertEqual(result.returncode,0,result.stderr[-3000:])

    def test_long_closed_traversal_replays_factored_calls_and_rejects_false_result(self):
        objects={}
        def put(declaration,deps=()):
            function=declaration.get('Function')
            interface=dict(parameters=dict(function['params']),result=function['result']) if function else {}
            obj=entry('definition',MATH,dict(declaration=declaration),deps,**interface)
            key=identity(obj);objects[key]=obj;return key
        rows=put({'Datatype':dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64','SelfType'])])})
        function=put({'Function':dict(params=[['rows',{'Data':rows}],['total','U64']],result='U64',recursive=0,
            body={'Match':dict(scrutinee=var('rows'),branches=[dict(bindings=[],body=var('total')),
                dict(bindings=['head','tail'],body={'SelfCall':[var('tail'),{'Binary':dict(op='+',left=var('total'),right=var('head'))}]})])})},[rows])
        chunks=FoldChunks(objects,[]);data=cons(rows,0,[])
        for number in range(72):data=cons(rows,1,[{'U64':number},data])
        data=chunks.share_data(data);term=call(function,[data,{'U64':(1<<64)-1}])
        evaluator=ClosedEquations(chunks);value,proof=evaluator.evaluate(term)
        expected=(sum(range(72))-1)&((1<<64)-1)
        self.assertEqual(value,{'U64':expected});self.assertGreater(len(evaluator.calls),64)
        theorem=chunks.theorem([],term,value,proof)
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary);source=folder/'source.ink';source.write_text('module closed_trace;fn f(x:u32)->u32{return x;}')
            core=folder/'core.json'
            result=subprocess.run([INK,'emit-core',source,'-o',core],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr)
            for good in [True,False]:
                imported=dict(chunks.objects);root=theorem
                if not good:
                    changed=copy.deepcopy(imported[theorem]);changed['payload']['declaration']['Theorem']['to']={'U64':expected^1}
                    changed['interface']['operations']=operations(changed['payload'])
                    root=identity(changed);imported[root]=changed
                store=Store.publish(folder/('valid'if good else 'invalid'),list(imported.values()))
                view=folder/'view.json';view.write_bytes(canonical(store.bundle([root])))
                result=subprocess.run([INK,'knowledge-check',core,view],capture_output=True,text=True,timeout=180)
                self.assertEqual(result.returncode==0,good,result.stderr[-3000:])

    def test_branch_laziness_live_inputs_and_cycles(self):
        abstract=entry('definition',MATH,{'declaration':{'AbstractFunction':dict(params=[],result='U64')}},result='U64')
        key=identity(abstract);chunks=FoldChunks({key:abstract},[])
        evaluator=ClosedEquations(chunks)
        term={'If':dict(condition={'Bool':True},on_true={'U64':7},on_false=call(key,[]))}
        self.assertEqual(evaluator.evaluate(term)[0],{'U64':7})
        with self.assertRaisesRegex(ValueError,'live inputs'):
            evaluator.evaluate(var('live'))
        with self.assertRaisesRegex(ValueError,'function/arity'):
            evaluator.evaluate(call(key,[]))
        # Invalid caller-supplied cyclic definitions are not source premises;
        # authoring still terminates before independent definition checking.
        chunks.objects['cycle']={'payload':{'declaration':{'Function':dict(params=[],result='U64',recursive=None,body=call('cycle',[]))}}}
        with self.assertRaisesRegex(ValueError,'cycle'):
            evaluator.evaluate(call('cycle',[]))


if __name__=='__main__':unittest.main()
