"""Projected fold authoring has no authority without source-step replay."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical


class SourceProjectedFold(unittest.TestCase):
    def test_state_projection_and_changed_projection_rejection(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        source = '''module projected;
record State{offset:u32,values:Buffer<u32>,}
fn step(s:State,item:u32)->State{return State{offset:s.offset,values:s.values.push(item+s.offset)};}
'''
        with tempfile.TemporaryDirectory() as temp:
            d = Path(temp)
            src = d / 'source.ink'
            src.write_text(source)
            core = d / 'core.json'
            result = subprocess.run([compiler, 'emit-core', src, '-o', core], capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            state = {'Value': {'Named': 'State'}}
            word = {'Value': 'U32'}
            item = {'sort': word, 'node': {'Bound': 0}}
            offset = {'sort': word, 'node': {'Op': ['field:offset', [
                {'sort': state, 'node': {'Bound': 1}}
            ]]}}
            for label, observed, accepted in [('valid', offset, True), ('false', item, False)]:
                body = {'sort': word, 'node': {'Op': ['binary:+', [item, observed]]}}
                projection = {'sort': {'Arrow': [state, {'Arrow': [word, word]}]},
                              'node': {'Lambda': {'sort': {'Arrow': [word, word]}, 'node': {'Lambda': body}}}}
                path = d / (label + '.json')
                path.write_text(json.dumps(projection))
                output = d / label
                result = subprocess.run([os.environ.get('INK_PYTHON', 'python3'),
                    root / 'tools/source_fold_observer.py', '--compiler', compiler, '--core', core,
                    '--transition', 'step', '--state-parameter', 's', '--item-parameter', 'item',
                    '--observer', 'values', '--append', '--state-projector', '--projector', path,
                    '-o', output], capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode == 0, accepted, result.stderr[-1800:])
                self.assertEqual(output.exists(), accepted)
                if accepted:
                    store = Store(output)
                    roots = list(json.loads((output / 'store/names.json').read_text()).values())
                    view = d / 'view.json'
                    view.write_bytes(canonical(store.bundle(roots)))
                    replay = subprocess.run([compiler, 'knowledge-check', core, view], capture_output=True, text=True, timeout=120)
                    self.assertEqual(replay.returncode, 0, replay.stderr)


if __name__ == '__main__':
    unittest.main()
