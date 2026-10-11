"""Reproduction and authenticated false-layout controls for ordinary candidates."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'producers'))
sys.path.insert(0, str(ROOT))
from representations import generate
from ink_knowledge import Store, identity
from ink_knowledge.store import operations


def wrong_bit(request, directory, mutator=None):
    objects = json.loads(json.dumps(request['knowledge']['objects']))
    def mutate(value):
        if isinstance(value, dict):
            b = value.get('Binary', {})
            if b.get('op') == '&' and b.get('right') == {'U64': 4}:
                b['right'] = {'U64': 2}
                return True
            return any(mutate(x) for x in value.values())
        if isinstance(value, list):
            return any(mutate(x) for x in value)
        return False
    assert any((mutator or mutate)(e['payload']['declaration']['Function']['body'])
               for e in objects.values() if 'Function' in e['payload'].get('declaration', {}))
    renamed, rebuilt, pending = {}, {}, dict(objects)
    def rewrite(value):
        if isinstance(value, str):
            if value.startswith('call:'):
                return 'call:' + renamed.get(value[5:], value[5:])
            return renamed.get(value, value)
        if isinstance(value, dict):
            return {k: rewrite(x) for k, x in value.items()}
        if isinstance(value, list):
            return [rewrite(x) for x in value]
        return value
    while pending:
        ready = [k for k,e in pending.items() if not any(d in pending for d in e['dependencies'])]
        assert ready
        for old in ready:
            e = rewrite(pending.pop(old))
            e['dependencies'] = sorted(set(e['dependencies']))
            e['interface']['operations'] = operations(e['payload']) if 'declaration' in e['payload'] else sorted(set(e['interface']['operations']))
            new = identity(e)
            renamed[old] = new
            rebuilt[new] = e
    rid = renamed[request['representation']]
    return dict(request, representation=rid,
                knowledge=Store.publish(directory, rebuilt.values()).bundle([rid]))


@unittest.skipUnless(os.environ.get('INK_COMPILER'), 'requires explicit compiler')
class ColumnLayoutTests(unittest.TestCase):
    def test_column_and_bit_layouts_reproduce(self):
        for label, packed in [('column-layouts', False), ('packed-booleans', True)]:
            directory = ROOT / 'research' / label
            model = json.loads((directory / 'model.json').read_text())
            with tempfile.TemporaryDirectory() as output:
                proposal = generate(model, output, columnar=True, packed_booleans=packed)
            for name, request in zip(['direct', 'reversed'], proposal['requests']):
                self.assertEqual(request, json.loads((directory / (name + '.json')).read_text()))

    def test_reauthenticated_wrong_bit_is_mathematically_rejected(self):
        directory = ROOT / 'research/packed-booleans'
        with tempfile.TemporaryDirectory() as output:
            request = wrong_bit(json.loads((directory / 'direct.json').read_text()), Path(output) / 'store')
            path = Path(output) / 'forged.json'
            path.write_text(json.dumps(request))
            result = subprocess.run([os.environ['INK_COMPILER'], 'check-representation',
                                     str(directory / 'source.ink'), str(path)], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('definitional computation does not prove equality', result.stderr)


if __name__ == '__main__':
    unittest.main()
