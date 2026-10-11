"""Admission failures must not move the canonical publication pointer."""
import copy
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from ink_knowledge import Store, identity, semantic_entry
from producers.performance_laws import named_laws as original_laws
from producers.web_numeric_laws import named_laws
from producers.publish_web_stack_laws import publish

KNOWLEDGE = Path(__file__).resolve().parents[1]
COMPILER = Path(os.environ.get('INK_COMPILER', KNOWLEDGE.parent / 'target/release/ink'))


@unittest.skipUnless(COMPILER.is_file(), 'release compiler required for mathematical admission')
class WebPublisherTests(unittest.TestCase):
    def initial(self, path):
        obj = semantic_entry(original_laws()[0][1])
        return Store.publish(path, [obj], {'prior': identity(obj)})

    def test_checked_extension_preserves_old_pin_and_names(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'knowledge'
            prior = self.initial(root)
            receipt = Path(directory) / 'receipt.json'
            result = publish(root, COMPILER, receipt, ['web_numeric_laws'], prior.snapshot_id)
            self.assertEqual(result['added_entries'], 24)
            self.assertEqual(result['entries'], 25)
            pinned = Store(root, root / 'store/snapshots' / (prior.snapshot_id + '.json'))
            self.assertEqual(set(prior.members()), set(pinned.members()))
            self.assertTrue(result['previous_snapshot_preserved'])
            self.assertEqual(len(result['admission']['entries']), 24)
            with self.assertRaisesRegex(ValueError, 'overwrite'):
                publish(root, COMPILER, receipt, ['web_numeric_laws'])

    def test_hash_valid_false_law_does_not_publish(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'knowledge'
            self.initial(root)
            before = {name: (root / 'store' / name).read_bytes()
                      for name in ['snapshot.json', 'names.json']}
            receipt = Path(directory) / 'receipt.json'
            forged = copy.deepcopy(dict(named_laws())['repeat_cubic_increment_u32'])
            forged['to'] = forged['from']['node']['Op'][1][1]
            with patch('producers.web_numeric_laws.named_laws', return_value=[('false', forged)]):
                with self.assertRaises(subprocess.CalledProcessError) as failure:
                    publish(root, COMPILER, receipt, ['web_numeric_laws'])
            self.assertIn('knowledge-check', str(failure.exception))
            self.assertIn('semantic normal forms differ', failure.exception.stderr)
            self.assertFalse(receipt.exists())
            for name, expected in before.items():
                self.assertEqual((root / 'store' / name).read_bytes(), expected)

    def test_extension_checks_previously_published_dependency_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)/'knowledge';prior=self.initial(root)
            base=original_laws()[0][1];identifier=identity(semantic_entry(base))
            reverse=copy.deepcopy(base);reverse['from'],reverse['to']=base['to'],base['from']
            reverse['dependencies']=[identifier]
            reverse['proof']={'Sym':{'Use':dict(law=identifier,arguments={name:dict(sort=sort,node={'Free':name}) for name,sort in base['params'].items()},premises=[])}}
            with patch('producers.web_numeric_laws.named_laws',return_value=[('reverse_dependency',reverse)]):
                result=publish(root,COMPILER,Path(directory)/'receipt.json',['web_numeric_laws'],prior.snapshot_id)
            self.assertEqual(result['added_entries'],1)
            self.assertEqual(set(result['admission']['entries']),{identifier,identity(semantic_entry(reverse))})


if __name__ == '__main__':
    unittest.main()
