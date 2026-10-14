"""Staging binds captured generations and uses the actual proof checker."""
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from ink_knowledge import Store, entry, identity
from producers import publish_web_pipeline33 as producer
from producers.semantic_laws import law, word


class PublicationStaging(unittest.TestCase):
    def setUp(self):
        self.compiler = Path(os.environ.get('INK_COMPILER', 'target/debug/ink')).resolve()
        if not self.compiler.is_file():
            self.skipTest('requires INK_COMPILER')
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.root = self.directory / 'knowledge'
        self.seed = entry('definition', 'staging-test', {'value': 7})
        self.original = Store.publish(self.root, [self.seed], {'seed': identity(self.seed)})
        self.rows = self.directory / 'rows.json'
        self.rows.write_text(json.dumps([dict(name='reflexivity', role='fresh',
            law=law({}, word('U32', 1), word('U32', 1)))]))
        self.staged = self.directory / 'staged'
        self.receipt = self.directory / 'published.json'

    def stage(self):
        receipt = producer.stage(self.root, self.compiler, self.rows, self.staged)
        self.assertEqual(receipt['status'], 'checked')
        commands = json.loads((self.staged / 'commands.json').read_bytes())
        self.assertTrue(any('knowledge-check' in command['argv'] for command in commands))
        self.assertTrue(all(command['exit_code'] == 0 for command in commands))
        return receipt

    def test_staging_and_publish_use_selected_names_despite_dirty_mirrors(self):
        (self.root / 'store/names.json').write_text('{broken mirror')
        receipt = self.stage()
        (self.staged / 'current/store/names.json').write_text('{broken staged mirror')
        result = producer.publish(self.root, self.staged, self.receipt)
        self.assertEqual(result['status'], 'published')
        self.assertEqual(Store(self.root).snapshot_id, receipt['snapshot'])
        self.assertEqual(Store(self.root).names['seed'], identity(self.seed))
        self.assertIn('web-stack/reflexivity', Store(self.root).names)

    def test_names_only_change_after_staging_rejects_without_losing_alias(self):
        self.stage()
        current = self.original.extend([], {'alias': identity(self.seed)})
        with self.assertRaises(ValueError):
            producer.publish(self.root, self.staged, self.receipt)
        self.assertEqual(Store(self.root).publication_id, current.publication_id)
        self.assertFalse(self.receipt.exists())

    def test_writer_between_staged_validation_and_commit_is_rejected(self):
        self.stage()
        original_publish = Store.publish
        raced = []
        def race(*args, **kwargs):
            raced.append(self.original.extend([], {'alias': identity(self.seed)}))
            return original_publish(*args, **kwargs)
        with patch.object(Store, 'publish', side_effect=race):
            with self.assertRaisesRegex(ValueError, 'publication changed before replacement'):
                producer.publish(self.root, self.staged, self.receipt)
        self.assertEqual(len(raced), 1)
        self.assertEqual(Store(self.root).publication_id, raced[0].publication_id)
        self.assertFalse(self.receipt.exists())


if __name__ == '__main__':
    unittest.main()
