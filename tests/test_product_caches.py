"""Reproduce composed source-bound proposals; admission remains compiler-owned."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'producers'))
from representations import generate
from representation_product import generate as product
from representation_bridge import generate as bridge


@unittest.skipUnless(os.environ.get('INK_COMPILER'), 'requires compiler for scalar certificates')
class ProductCacheTests(unittest.TestCase):
    def test_frozen_proposals_and_both_migrations_reproduce(self):
        directory = ROOT / 'research/product-caches'
        read = lambda name: json.loads((directory / (name + '.json')).read_text())
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            components = []
            for name in ['zero', 'one']:
                component = generate(read('model'), output / name, cache_query=name,
                                     preserve_cache=True, dynamic_delta=True)['requests'][1]
                self.assertEqual(component, read(name))
                components.append(component)
            composed = product(read('model'), components, output / 'product', {'one': 1})
            self.assertEqual(composed, read('product'))
            for name, a, b in [('forward', components[0], composed),
                               ('backward', composed, components[0])]:
                self.assertEqual(bridge(a, b, output / name, True), read(name))

    def test_component_source_and_selection_bounds_are_checked(self):
        directory = ROOT / 'research/product-caches'
        read = lambda name: json.loads((directory / (name + '.json')).read_text())
        with tempfile.TemporaryDirectory() as output:
            with self.assertRaises(ValueError):
                product(read('model'), [read('zero')], output)
            with self.assertRaises(ValueError):
                product(read('model'), [read('zero'), read('one')], output, {'one': 2})
            wrong = read('one')
            wrong['input_core_sha256'] = '0' * 64
            with self.assertRaises(ValueError):
                product(read('model'), [read('zero'), wrong], output)


if __name__ == '__main__':
    unittest.main()
