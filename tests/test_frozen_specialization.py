import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from producers.frozen_specialization import Partial, specialize

ROOT = Path(__file__).resolve().parents[2]
INK = Path(os.environ.get('INK_COMPILER', ROOT/'target/debug/ink'))


class FrozenSpecialization(unittest.TestCase):
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
