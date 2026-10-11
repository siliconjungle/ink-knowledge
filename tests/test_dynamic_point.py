"""Reproduce external authoring bytes; the Ink checker grants admission."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'producers'))
from representations import generate


@unittest.skipUnless(os.environ.get('INK_COMPILER'), 'requires explicit compiler for scalar certificates')
class DynamicPointTests(unittest.TestCase):
    def test_frozen_source_bound_proposal_is_reproducible(self):
        directory = ROOT / 'research/dynamic-point'
        model = json.loads((directory / 'model.json').read_text())
        with tempfile.TemporaryDirectory() as output:
            proposal = generate(model, output, cache_query='zero', preserve_cache=True,
                                dynamic_delta=True)
        for label, request in zip(['direct', 'delta'], proposal['requests']):
            self.assertEqual(request, json.loads((directory / (label + '.json')).read_text()))
        self.assertEqual(proposal['migration'], json.loads((directory / 'migration.json').read_text()))


if __name__ == '__main__':
    unittest.main()
