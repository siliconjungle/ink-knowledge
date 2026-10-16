import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from producers.frozen_specialization import Partial, literal, specialize
from producers.point_delta import normal

ROOT = Path(__file__).resolve().parents[2]
INK = Path(os.environ.get('INK_COMPILER', ROOT/'target/debug/ink'))


class FrozenSpecialization(unittest.TestCase):
    def test_f32_literals_preserve_bits_and_scalar_equality_uses_ieee_rules(self):
        p = dict(functions=[], states=[], enums={}, records={})
        partial = Partial(p)
        for bits in [0, 0x80000000, 1, 0x80000001, 0x007fffff, 0x00800000,
                     0x3f800001, 0x7f7fffff, 0x7f800000, 0xff800000,
                     0x7fc01234, 0x7fa01234, 0xffc05678]:
            value = literal('F32', {'F32Bits': bits}, p)
            self.assertEqual(value, {'Call': ['f32_from_bits', [{'Num': bits}]]}
                             if bits & 0x7f800000 == 0x7f800000 else {'Float': bits})
            self.assertTrue(partial.value(value))
            self.assertFalse(partial.value(value, equality=True))
            for other_bits in [bits,0x80000000,0]:
                other=literal('F32',{'F32Bits':other_bits},p)
                nan=lambda word:word & 0x7f800000==0x7f800000 and word & 0x7fffff!=0
                equal=not(nan(bits) or nan(other_bits)) and (bits==other_bits or bits & 0x7fffffff==other_bits & 0x7fffffff==0)
                for op in ['==', '!=']:
                    expression = {'Binary': [op, value, other]}
                    self.assertEqual(partial.expr(expression), {'Bool':equal if op=='==' else not equal})
                    record = {'Record': ['R', [['x', value]]]}
                    wrapped = {'Binary': [op, record, record]}
                    self.assertEqual(partial.expr(wrapped), wrapped)
        self.assertEqual(literal('F32', 0.1, p), {'Float': 0x3dcccccd})
        self.assertEqual(literal('F32', -0.0, p), {'Float': 0x80000000})
        for bad in [True, '0.1', {'F32Bits': -1}, {'F32Bits': 1 << 32},
                    {'F32Bits': True}, {'F32Bits': 0, 'extra': 1}, float('nan'), float('inf'), 1e100]:
            with self.assertRaises(ValueError):
                literal('F32', bad, p)
        with self.assertRaises(ValueError):
            literal('F64', {'F64Bits': '0'}, p)

    def test_dynamic_floating_and_unknown_operators_remain_ordinary_core_terms(self):
        for op in ['f32:+', 'f32:*', 'f32:==', 'f32:!=', 'f32:neg', 'f32:sqrt', 'unknown']:
            expression = {'Binary': dict(op=op, left={'Var':'dynamic'}, right={'U64': 0})}
            self.assertEqual(normal(expression, {}), expression)
        expression={'Binary':dict(op='unknown',left={'U64':0},right={'U64':0})}
        self.assertEqual(normal(expression,{}),expression)

    def test_closed_maps_and_numeric_casts_keep_bounds_and_lazy_callbacks(self):
        partial=Partial(dict(functions=[],states=[],enums={},records={}))
        rows={'Call':['list',[{'Float':0x3f800000},{'Float':0x40000000}]]}
        callback={'Lambda':['x',{'Binary':['*',{'Var':'x'},{'Float':0x40000000}]}]}
        expression={'Method':[rows,'map',[callback]]}
        self.assertEqual(partial.expr(expression),{'Call':['list',[{'Float':0x40000000},{'Float':0x40800000}]]})
        unknown={'Lambda':['x',{'Call':['unknown',[{'Var':'x'}]]}]}
        self.assertEqual(partial.expr({'Method':[{'Call':['list',[]]},'map',[unknown]]}),{'Call':['list',[]]})
        residual={'Method':[rows,'map',[unknown]]}
        self.assertEqual(partial.expr(residual),residual)
        captured={'Method':[rows,'map',[{'Lambda':['x',{'Binary':['+',{'Var':'x'},{'Var':'live'}]}]}]]}
        self.assertEqual(partial.expr(captured),captured)
        for name,bad in [('f32_from_u32',1<<32),('f32_from_bits',1<<32),('f32_from_u64',1<<64),('f32_from_i32',1<<31)]:
            self.assertIsNone(partial.constant_call(name,[{'Num':bad}]))
        self.assertEqual(partial.constant_call('f32_from_i32',[{'Neg':{'Num':1<<31}}]),{'Float':0xcf000000})
        self.assertIsNone(partial.constant_call('f32_from_i32',[{'Neg':{'Num':(1<<31)+1}}]))

    def test_frozen_float_records_specialize_structure_and_replay_complete_actions(self):
        source = '''module float_structure;
enum Kind { Affine, Shift, }
record Kernel { kind:Kind,scale:f32,bias:f32, }
state Model:Table<u64,Kernel>=Table.empty();
state Live:Table<u64,f32>=Table.empty();
event Changed:f32;
fn evaluate(k:Kernel,x:f32)->f32 {
 return choose(k.kind==Kind.Affine,x*k.scale+k.bias,x+k.scale);
}
query serve(x:f32)->f32 reads(Model,Live) {
 let k=Model.get(0).unwrap_or(Kernel{kind:Kind.Affine,scale:1.0,bias:0.0});
 return evaluate(k,x)+Live.get(0).unwrap_or(0.0);
}
query self_equal()->Bool reads(Model) {
 let k=Model.get(0).unwrap_or(Kernel{kind:Kind.Affine,scale:1.0,bias:0.0});
 return k.scale==k.scale;
}
query is_zero()->Bool reads(Model) {
 let k=Model.get(0).unwrap_or(Kernel{kind:Kind.Affine,scale:1.0,bias:0.0});
 return k.scale==0.0;
}
query raw()->u32 reads(Model) {
 let k=Model.get(0).unwrap_or(Kernel{kind:Kind.Affine,scale:1.0,bias:0.0});
 return f32_bits(k.scale);
}
change set(value:f32)->Unit writes(Live) emits(Changed) {Live.put(0,value);emit Changed(value);return ();}
'''
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            src, core = temp/'source.ink', temp/'core.json'
            src.write_text(source)
            subprocess.run([INK, 'emit-core', src, '-o', core], check=True, capture_output=True)
            original = json.loads(core.read_bytes())
            for i, bits in enumerate([0, 0x80000000, 1, 0x3f000001, 0x7f800000, 0x7fa01234]):
                frozen = json.loads(json.dumps(original))
                frozen['semantics'] = 'ink-executable-core-v14'
                frozen['program']['frozen'] = {'Model': [[0, dict(kind='Kind.Affine' if i % 2 else 'Kind.Shift',
                    scale={'F32Bits': bits}, bias={'F32Bits': 0x3e800000})]]}
                core.write_text(json.dumps(frozen))
                candidate = specialize(frozen)
                serve = next(a for a in candidate['program']['actions'] if a['name'] == 'serve')
                body = json.dumps(serve['body'])
                self.assertNotIn('"Model"', body)
                self.assertNotIn('"evaluate"', body)
                self.assertNotIn('"kind"', body)
                # Only scalar IEEE comparison collapses; the complete action
                # proof still has to replay its NaN and signed-zero behavior.
                equal = next(a for a in candidate['program']['actions'] if a['name'] == 'self_equal')
                self.assertNotIn('"Binary"', json.dumps(equal['body']))
                packet = temp/'selection.json'
                subprocess.run(['python3', ROOT/'knowledge/producers/frozen_specialization.py',
                                core, '--ink', INK, '-o', packet], check=True, capture_output=True)
                forged = json.loads(packet.read_bytes())
                serve = next(a for a in forged['action_replacement']['selected']['program']['actions'] if a['name'] == 'serve')
                def change_coefficient(e):
                    if isinstance(e, dict):
                        if 'Float' in e:
                            e['Float'] ^= 1
                            return True
                        return any(change_coefficient(x) for x in e.values())
                    return isinstance(e, list) and any(change_coefficient(x) for x in e)
                self.assertTrue(change_coefficient(serve['body']))
                bad = temp/'wrong-coefficient.json'
                bad.write_text(json.dumps(forged))
                rejected = subprocess.run([INK, 'check-selection', core, bad], capture_output=True)
                self.assertNotEqual(rejected.returncode, 0, 'a changed coefficient reused its old proof')
                steps = [dict(call='self_equal', args=[]), dict(call='is_zero', args=[]), dict(call='raw', args=[])]
                for x in [0, 0x80000000, 0x3dcccccd, 0x7fa05678]:
                    steps.extend([dict(call='set', args=[{'F32Bits': x}]), dict(call='serve', args=[{'F32Bits': x}])])
                script = temp/'script.json'
                script.write_text(json.dumps(steps))
                outputs, checkpoints = [], []
                for selected in [False, True]:
                    snapshot = temp/f'{selected}.snapshot'
                    command = [INK, 'execute', core, script, '--core', '--portable', '--snapshot-out', snapshot]
                    if selected:
                        command += ['--selection', packet]
                    output = subprocess.run(command, check=True, capture_output=True)
                    outputs.append(json.loads(output.stdout));checkpoints.append(snapshot.read_bytes())
                self.assertEqual(outputs[0], outputs[1])
                self.assertEqual(checkpoints[0], checkpoints[1])

    def test_effectful_dynamic_argument_is_bound_once_and_checked(self):
        source = """module dynamic_arguments;
state Mode:Table<u64,Bool>=Table.empty();
state Ticks:Table<u64,u64>=Table.empty();
event seen:u64;
fn select(mode:Bool,x:u64)->u64 {
 let shadow=choose(mode,x,x+1);
 return shadow;
}
change tick(fail:Bool)->Result<u64,u64> reads(Ticks) writes(Ticks) emits(seen) {
 let next=Ticks.get(0).unwrap_or(0)+1;
 Ticks.put(0,next);emit seen(next);
 if fail {return Err(99);}
 return Ok(next);
}
change work(fail:Bool)->Result<u64,u64> reads(Mode,Ticks) writes(Ticks) emits(seen) {
 return Ok(select(Mode.get(0).unwrap_or(false),tick(fail)?));
}
"""
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            src, core, packet = temp/'source.ink', temp/'core.json', temp/'selection.json'
            src.write_text(source)
            subprocess.run([INK, 'emit-core', src, '-o', core], check=True, capture_output=True)
            original = json.loads(core.read_bytes())
            original['semantics'] = 'ink-executable-core-v14'
            original['program']['frozen'] = {'Mode': [[0, True]]}
            core.write_text(json.dumps(original))
            selected = specialize(original)
            body = json.dumps(selected['program']['actions'][1]['body'])
            self.assertEqual(body.count('"tick"'), 1)
            self.assertNotIn('"select"', body)
            subprocess.run(['python3', ROOT/'knowledge/producers/frozen_specialization.py',
                            core, '--ink', INK, '-o', packet], check=True, capture_output=True)
            script = temp/'script.json'
            script.write_text(json.dumps([dict(call='work', args=[False]),
                                          dict(call='work', args=[True]),
                                          dict(call='work', args=[False])]))
            outputs = []
            checkpoints = []
            for selected in (False, True):
                snapshot = temp/('selected.snapshot' if selected else 'baseline.snapshot')
                command = [INK, 'execute', core, script, '--core', '--portable', '--snapshot-out', snapshot]
                if selected:
                    command += ['--selection', packet]
                result = subprocess.run(command, check=True, capture_output=True)
                outputs.append(json.loads(result.stdout))
                checkpoints.append(snapshot.read_bytes())
            self.assertEqual(outputs[0], outputs[1])
            self.assertEqual(checkpoints[0], checkpoints[1])

    def test_eager_nonliteral_default_survives(self):
        p = dict(functions=[], states=[], enums={}, records={}, frozen={})
        partial = Partial(p)
        expression = {'Method': [{'Call': ['Some', [{'Num': 7}]]},
                                  'unwrap_or', [{'Call': ['observable', []]}]]}
        self.assertEqual(partial.expr(expression), expression)

    def test_trainable_metadata_is_not_an_immutable_fact(self):
        p = dict(functions=[], states=[dict(name='Choice', ty={'Table': ['U64', 'U64']})],
                 actions=[dict(body=[{'Return': {'Method': [{'Var': 'Choice'}, 'get', [{'Num': 0}]]}}])],
                 enums={}, records={}, contracts=dict(learning=dict(trainable=['Choice'])))
        source = dict(schema=1, semantics='ink-executable-core-v1', program=p)
        self.assertEqual(specialize(source), source)

    def test_inline_names_avoid_every_source_identifier(self):
        p = dict(functions=[], states=[], enums={}, records={},
                 marker='__frozen_proposal_0')
        partial = Partial(p)
        self.assertEqual(partial.fresh(), '__frozen_proposal_1')


if __name__ == '__main__':
    unittest.main()
