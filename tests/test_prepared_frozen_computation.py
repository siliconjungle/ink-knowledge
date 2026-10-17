"""Prepared application structure needs source checking and complete proofs."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from producers.closed_reference_calls import ReferenceCalls, argument_value
from producers.frozen_composition import ChunkPartial, propose_source
from producers import frozen_composition
from producers.frozen_specialization import Partial, literal

ROOT = Path(__file__).resolve().parents[2]
INK = Path(os.environ.get('INK_COMPILER', ROOT/'target/debug/ink')).resolve()


class PreparedFrozenComputation(unittest.TestCase):
    def test_sum_callbacks_select_one_arm_and_keep_dynamic_captures(self):
        p = Partial(dict(functions=[], states=[], enums={}, records={}))
        selected = {'Lambda': ['x', {'Binary': ['+', {'Var': 'x'}, {'Var': 'live'}]}]}
        unused = {'Lambda': ['x', {'Var': 'never_visit'}]}
        p.keeps['never_visit'] = {'Var': 'never_visit'}
        some = {'Call': ['Some', [{'Float': 0x80000000}]]}
        expected = {'Binary': ['+', {'Float': 0x80000000}, {'Var': 'live'}]}
        self.assertEqual(p.expr({'Method': [some, 'fold', [selected, unused]]}), expected)
        self.assertEqual(p.expr({'Method': [some, 'map', [selected]]}), {'Call': ['Some', [expected]]})
        self.assertEqual(p.expr({'Method': [{'Var': 'None'}, 'map', [unused]]}), {'Var': 'None'})
        err = {'Call': ['Err', [{'String': 'failed'}]]}
        self.assertEqual(p.expr({'Method': [err, 'map', [unused]]}), err)
        self.assertEqual(p.expr({'Method': [err, 'map_err', [{'Lambda': ['x', {'Var': 'x'}]}]]}), err)
        self.assertEqual(p.expr({'Try': {'Call': ['Ok', [{'Float': 1}]]}}), {'Float': 1})
        self.assertEqual(p.expr({'Try': err}), {'Try': err})

    def test_keep_values_do_not_capture_local_binders_or_cache_live_reads(self):
        program = dict(functions=[], states=[], enums={}, records={}, keeps=[
            dict(name='K', value={'Float': 0x3f800000}),
            dict(name='Live', value={'Var': 'state'}),
            dict(name='Cycle', value={'Var': 'Cycle'})])
        p = Partial(program)
        self.assertEqual(p.expr({'Var': 'K'}), {'Float': 0x3f800000})
        self.assertEqual(p.expr({'Lambda': ['K', {'Var': 'K'}]}), {'Lambda': ['K', {'Var': 'K'}]})
        dynamic = {'Let': ['K', 'F32', {'Var': 'input'}, {'Var': 'K'}]}
        self.assertEqual(p.expr(dynamic), dynamic)
        for name in ['Live', 'Cycle']:
            self.assertEqual(p.expr({'Var': name}), {'Var': name})
            self.assertNotIn(name, p.keep_values)

    def test_reference_argument_bits_failures_and_call_budget(self):
        program = dict(functions=[dict(name='closed', params=[['x','F32']], result='F32')],
                       states=[], enums={}, records={})
        for bits in [0, 0x80000000, 1, 0x7fa01234, 0xff800000]:
            self.assertEqual(argument_value('F32', literal('F32', {'F32Bits': bits}, program), program),
                             {'F32Bits': bits})
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory)/'source.json'
            source.write_text(json.dumps(dict(program=program)))
            evaluator = ReferenceCalls(source, INK)
            with patch('producers.closed_reference_calls.subprocess.run', side_effect=subprocess.TimeoutExpired('ink',30)) as run:
                self.assertIsNone(evaluator('closed', [{'Float': 0}]))
                self.assertIsNone(evaluator('closed', [{'Float': 0}]))
                self.assertEqual(run.call_count, 1)
                for bits in range(1, 30):
                    self.assertIsNone(evaluator('closed', [{'Float': bits}]))
                self.assertEqual(run.call_count, evaluator.MAX_CALLS)
            self.assertIsNone(evaluator('generated_helper', [{'Float': 0}]))

    def test_unique_helper_budget_allows_reuse_and_action_failure_rolls_back(self):
        p = ChunkPartial(dict(functions=[], states=[], enums={}, records={}, ids={}))
        function = dict(name='one', params=[['x','U32']], result='U32', body={'Var':'x'})
        self.assertEqual(p.intern(function), 'one')
        with patch('producers.frozen_composition.FoldChunks.MAX_HELPERS', 1):
            self.assertEqual(p.intern(dict(function, name='two')), 'one')
            with self.assertRaisesRegex(ValueError, 'helper budget'):
                p.intern(dict(function, name='three', body={'Num': 1}))
        source = dict(program=dict(functions=[], states=[], enums={}, records={}, ids={}, actions=[
            dict(name='first', params=[], body=[{'Return': {'Num':1}}]),
            dict(name='second', params=[], body=[{'Return': {'Num':2}}])]))
        original = copy.deepcopy(source)
        real = ChunkPartial.statements
        def statements(partial, body, env):
            if body[0]['Return'] == {'Num':2}:
                partial.intern(function)
                raise ValueError('frozen composition helper budget')
            return real(partial, body, env)
        with patch.object(ChunkPartial, 'statements', statements):
            selected, helpers = propose_source(source)
        self.assertEqual(selected, original)
        self.assertEqual(helpers, [])

    def test_prepared_result_graph_replays_complete_plan_and_rejects_wrong_literal(self):
        source = '''module prepared_graph;
state Code:Table<u64,Result<List<u32>,String>>=Table.empty();
trainable state Weight:Table<u64,u32>=Table.empty();
keep Default:Result<List<u32>,String>=make();
keep Prepared:Result<List<u32>,String>=Code.get(0).unwrap_or(Default);
fn make()->Result<List<u32>,String>{return Ok([1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]);}
fn evaluate(code:List<u32>,input:u32,w:u32)->u32{
 return foldl(code,input,fn(op)=>fn(total)=>total*w+op);
}
adaptive query serve(input:u32)->Result<u32,String> reads(Code,Weight,Prepared){
 let code=Prepared?;
 return Ok(evaluate(code,input,Weight.get(0).unwrap_or(1)));
}
learn change retune(w:u32)->Unit writes(Weight){Weight.put(0,w);return ();}
'''
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory); ink=folder/'source.ink';ink.write_text(source)
            core=folder/'source.json';plan=folder/'plan.json'
            def run(*args, success=True):
                r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=180)
                self.assertEqual(r.returncode == 0, success, r.stderr[-4000:])
                return r
            run(INK,'emit-core',ink,'-o',core)
            data=json.loads(core.read_bytes());data['semantics']='ink-executable-core-v14'
            data['program']['frozen']={'Code':[[0,{'Ok':list(range(1,17))}]]}
            core.write_text(json.dumps(data))
            proposed,helpers=propose_source(data,closed_call=ReferenceCalls(core,INK))
            self.assertTrue(helpers)
            serve=next(a for a in proposed['program']['actions'] if a['name']=='serve')
            self.assertNotIn('Prepared',json.dumps(serve['body']))
            run(INK,'check-core',core)
            run('python3',ROOT/'knowledge/producers/frozen_composition.py',core,'--ink',INK,'-o',plan)
            for name,options in [('baseline',[]),('selected',['--plan',plan])]:
                run(INK,'compile' if options else 'build',core,'--core',*options,
                    '--target','javascript','-o',folder/(name+'.mjs'))
            script=folder/'check.mjs';script.write_text('''import assert from 'node:assert/strict';
import {createState as a} from './baseline.mjs';import {createState as b} from './selected.mjs';
const x=a(),y=b();
for(const w of [0,1,2,4294967295]){
 assert.deepEqual(x.invoke('retune',[w]),y.invoke('retune',[w]));
 for(const input of [0,1,17,4294967295]){
  assert.deepEqual(x.invoke('serve',[input]),y.invoke('serve',[input]));
  assert.deepEqual(await x.checkpoint(),await y.checkpoint());
 }
}''')
            run('node',script)
            packet=json.loads(plan.read_bytes())
            serve=next(a for a in packet['steps'][1]['package']['action_replacement']['selected']['program']['actions'] if a['name']=='serve')
            serve['body']=[{'Return':{'Call':['Ok',[{'Num':123}]]}}]
            bad=folder/'wrong.json';bad.write_text(json.dumps(packet))
            run(INK,'check-plan',core,bad,'--core',success=False)
            # An evaluator is only a proposer: a false evaluated default must
            # fail the complete action proof and retain the prior publication.
            data['program']['frozen']={'Code':[]}
            core.write_text(json.dumps(data))
            retained=folder/'retained.json';retained.write_text('previous publication')
            false_value={'Call':['Ok',[{'Call':['list',[{'Num':99}]*16]}]]}
            def wrong_call(name, arguments):
                return copy.deepcopy(false_value) if name == 'make' else None
            with patch('sys.argv',['frozen_composition',str(core),'--ink',str(INK),'-o',str(retained)]), \
                    patch('producers.closed_reference_calls.ReferenceCalls',return_value=wrong_call):
                with self.assertRaises((ValueError,subprocess.CalledProcessError)):
                    frozen_composition.main()
            self.assertEqual(retained.read_text(),'previous publication')


if __name__ == '__main__':
    unittest.main()
