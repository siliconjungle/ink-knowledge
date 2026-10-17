"""Factored computation must transport each real proof premise."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store,canonical,identity
from ink_knowledge.store import entry
from producers.action_replacement import MATH,call,cons,var
from producers.computation_equality import ComputationEquality
from producers.fold_chunks import FoldChunks

ROOT=Path(__file__).resolve().parents[2]
INK=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()


class ConditionalComputation(unittest.TestCase):
    def test_case_facts_remain_conditions_and_cannot_be_reused_as_truth(self):
        objects={}
        def put(declaration,deps=()):
            function=declaration.get('Function',declaration.get('AbstractFunction'))
            interface=dict(parameters=dict(function['params']),result=function['result']) if function else {}
            obj=entry('definition',MATH,dict(declaration=declaration),deps,**interface)
            key=identity(obj);objects[key]=obj;return key
        option=put({'Datatype':dict(constructors=[dict(name='None',fields=[]),dict(name='Some',fields=['U64'])])})
        peek=put({'AbstractFunction':dict(name='peek',params=[['row','U64']],result={'Data':option})},[option])
        contains=put({'Function':dict(params=[['row','U64']],result='Bool',recursive=None,body={
            'Match':dict(scrutinee=call(peek,[var('row')]),branches=[dict(bindings=[],body={'Bool':False}),
                dict(bindings=['payload'],body={'Bool':True})])})},[option,peek])
        get=put({'Function':dict(params=[['row','U64']],result='U64',recursive=None,body={
            'Match':dict(scrutinee=call(peek,[var('row')]),branches=[dict(bindings=[],body={'U64':0}),
                dict(bindings=['payload'],body=var('payload'))])})},[option,peek])
        chunks=FoldChunks(objects,[]);equality=ComputationEquality(chunks)
        expression={'If':dict(condition=call(contains,[var('row')]),on_true=call(get,[var('row')]),on_false={'U64':7})}
        roots=[]
        noise=dict(**{'from':{'Bool':True},'to':{'Bool':True}})
        for value,expected in [(cons(option,1,[var('payload')]),var('payload')),(cons(option,0,[]),{'U64':7})]:
            condition=dict(**{'from':call(peek,[var('row')]),'to':value})
            equality.conditions=[(noise,0),(condition,1)]
            proof=equality.prove(expression,expected,dict(row='U64',payload='U64'),2)
            root=chunks.theorem([['row','U64'],['payload','U64']],expression,expected,proof,conditions=[noise,condition])
            self.assertEqual(chunks.objects[root]['payload']['declaration']['Theorem']['conditions'],[condition])
            roots.append(root)
        self.assertNotEqual(*roots)
        value=call(peek,[var('row')])
        case={'Cases':dict(scrutinee=value,**{'from':value,'to':value},cases=[
            dict(bindings=bindings,proof={'Trans':[{'Hypothesis':2},{'Sym':{'Hypothesis':2}}]})
            for bindings in [[],['case_payload']]])}
        local_root=chunks.theorem([['row','U64']],value,value,case,conditions=[noise,noise])
        self.assertEqual(chunks.objects[local_root]['payload']['declaration']['Theorem']['conditions'],[])
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary);source=folder/'source.ink';source.write_text('module scope;fn f(x:u32)->u32{return x;}')
            core=folder/'core.json';result=subprocess.run([INK,'emit-core',source,'-o',core],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr)
            for good in [True,False]:
                active=[*roots,local_root]
                if not good:
                    theorem=chunks.objects[roots[0]]['payload']['declaration']['Theorem']
                    active=[chunks.theorem(theorem['params'],theorem['from'],theorem['to'],theorem['proof'])]
                store=Store.publish(folder/('valid' if good else 'invalid'),list(chunks.objects.values()))
                view=folder/'view.json';view.write_bytes(canonical(store.bundle(active)))
                result=subprocess.run([INK,'knowledge-check',core,view],capture_output=True,text=True,timeout=180)
                self.assertEqual(result.returncode==0,good,result.stderr[-3000:])


if __name__=='__main__':unittest.main()
