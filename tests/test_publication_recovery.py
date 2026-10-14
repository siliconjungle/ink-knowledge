"""Real Store readers remain coherent across failed or terminated publishers."""
import json
import multiprocessing
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from ink_knowledge import Store, canonical, entry, identity
from ink_knowledge import publication


def value(name):
    return entry('definition', 'publication-recovery-test', {'name': name})


def paused_writer(root, boundary, ready, release):
    original = publication.replace
    added = value('added')
    def replace(path, data):
        original(path, data)
        if path.name == boundary:
            ready.set()
            if not release.wait(20):
                raise RuntimeError('publication release timeout')
    with patch.object(publication, 'replace', side_effect=replace):
        Store(root).extend([added], {'added': identity(added)})


class PublicationRecovery(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.seed = value('seed')
        self.old = Store.publish(self.root, [self.seed], {'seed': identity(self.seed)})

    def test_exception_at_each_precommit_replace_keeps_prior_reader_generation(self):
        added = value('added')
        for boundary in ['names.json', 'snapshot.json', 'publication.json']:
            with self.subTest(boundary=boundary):
                original = publication.replace
                def fail(path, data):
                    if path.name == boundary:
                        raise OSError('injected write failure')
                    return original(path, data)
                with patch.object(publication, 'replace', side_effect=fail):
                    with self.assertRaisesRegex(OSError, 'injected'):
                        self.old.extend([added], {'added': identity(added)})
                current = Store(self.root)
                self.assertEqual(current.publication_id, self.old.publication_id)
                self.assertEqual(current.names, self.old.names)
                self.assertEqual(set(current.members()), {identity(self.seed)})
                Store.recover(self.root)
                self.assertEqual(json.loads((self.old.data / 'names.json').read_bytes()), self.old.names)

    def test_killed_writer_leaves_complete_generation_and_lock_is_reusable(self):
        context = multiprocessing.get_context('spawn')
        for boundary in ['names.json', 'snapshot.json', 'publication.json']:
            with self.subTest(boundary=boundary), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                old = Store.publish(root, [self.seed], self.old.names)
                ready, release = context.Event(), context.Event()
                process = context.Process(target=paused_writer, args=(root, boundary, ready, release))
                process.start()
                try:
                    self.assertTrue(ready.wait(15))
                    selected = Store(root)
                    expected = dict(self.old.names)
                    if boundary == 'publication.json':
                        expected['added'] = identity(value('added'))
                    self.assertEqual(selected.names, expected)
                    self.assertEqual(set(selected.members()), set(expected.values()))
                    process.terminate()
                    process.join(10)
                    self.assertFalse(process.is_alive())
                    self.assertTrue(Store.recover(root))
                    self.assertEqual(Store(root).publication_id, selected.publication_id)
                    self.assertEqual(json.loads((old.data / 'names.json').read_bytes()), expected)
                    self.assertEqual(json.loads((old.data / 'snapshot.json').read_bytes()), selected.snapshot)
                    later = value('later')
                    final = Store(root).extend([later], {'later': identity(later)})
                    self.assertEqual(final.names, dict(expected, later=identity(later)))
                finally:
                    if process.is_alive():
                        process.terminate()
                    process.join(10)

    def test_failed_rollback_and_corrupt_mirrors_do_not_change_selection(self):
        original = publication.replace
        writes = []
        def fail(path, data):
            writes.append(path.name)
            if len(writes) > 1:
                raise OSError('persistent device failure')
            return original(path, data)
        with patch.object(publication, 'replace', side_effect=fail):
            with self.assertRaises(OSError):
                self.old.extend([value('added')], {'added': identity(value('added'))})
        self.assertNotEqual(json.loads((self.old.data / 'names.json').read_bytes()), self.old.names)
        (self.old.data / 'snapshot.json').write_text('{invalid')
        self.assertEqual(Store(self.root).publication_id, self.old.publication_id)
        self.assertEqual(Store(self.root).names, self.old.names)
        Store.recover(self.root)
        self.assertEqual(json.loads((self.old.data / 'snapshot.json').read_bytes()), self.old.snapshot)

    def test_names_only_change_pins_lazy_aliases_and_changes_generation_identity(self):
        held = Store(self.root)
        with patch.object(publication, 'load_names', side_effect=AssertionError('eager names read')):
            Store(self.root)
        new = held.extend([], {'alias': identity(self.seed)})
        self.assertEqual(held.snapshot_id, new.snapshot_id)
        self.assertNotEqual(held.publication_id, new.publication_id)
        self.assertEqual(held.names, {'seed': identity(self.seed)})
        self.assertEqual(new.names, dict(held.names, alias=identity(self.seed)))
        external = new.names
        external.clear()
        self.assertIn('alias', new.names)
        # A no-op stale extension must return the fresh aliases merged under lock.
        self.assertEqual(held.extend([]).publication_id, new.publication_id)

    def test_legacy_bootstrap_racing_pair_read_selects_complete_new_generation(self):
        (self.old.data / 'publication.json').unlink()
        original = publication.read
        triggered = []
        def read(path):
            if path == self.old.data / 'names.json' and not triggered:
                triggered.append(True)
                self.old.extend([value('added')], {'added': identity(value('added'))})
            return original(path)
        with patch.object(publication, 'read', side_effect=read):
            captured = Store(self.root)
        self.assertEqual(set(captured.names.values()), set(captured.members()))
        self.assertIn('added', captured.names)

    def test_failed_initial_publication_stays_unpublished_and_can_retry(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = publication.replace
            def fail(path, data):
                if path.name == 'snapshot.json':
                    raise OSError('initial snapshot failure')
                return original(path, data)
            with patch.object(publication, 'replace', side_effect=fail):
                with self.assertRaises(OSError):
                    Store.publish(root, [self.seed], self.old.names)
            self.assertFalse(Store.is_published(root))
            with self.assertRaises(FileNotFoundError):
                Store(root)
            retried = Store.publish(root, [self.seed], self.old.names)
            self.assertEqual(retried.names, self.old.names)

    def test_conditional_replacement_rejects_names_only_stale_generation(self):
        newer = self.old.extend([], {'alias': identity(self.seed)})
        self.assertEqual(newer.snapshot_id, self.old.snapshot_id)
        with self.assertRaisesRegex(ValueError, 'publication changed before replacement'):
            Store.publish(self.root, [self.seed], self.old.names,
                          expected_publication=self.old.publication_id)
        self.assertEqual(Store(self.root).publication_id, newer.publication_id)
        replaced = Store.publish(self.root, [self.seed], {'renamed': identity(self.seed)},
                                 expected_publication=newer.publication_id)
        self.assertEqual(replaced.names, {'renamed': identity(self.seed)})

    def test_names_tampering_rejects_and_explicit_snapshot_remains_exact(self):
        pin = self.old.data / 'snapshots' / (self.old.snapshot_id + '.json')
        new = self.old.extend([value('added')], {'added': identity(value('added'))})
        historical = Store(self.root, pin)
        self.assertEqual(historical.snapshot_id, self.old.snapshot_id)
        self.assertEqual(historical.names, self.old.names)
        selected, _ = publication.capture(self.old.data)
        (self.old.data / 'names' / (selected['names'] + '.json')).write_bytes(canonical({}))
        with self.assertRaisesRegex(ValueError, 'names content mismatch'):
            Store(self.root).names
        (self.old.data / 'publication.json').write_text('{invalid')
        with self.assertRaises(ValueError):
            Store(self.root)
        # Exact immutable pins do not depend on the health of the current pointer.
        self.assertEqual(Store(self.root, pin).object(identity(self.seed)), self.seed)
        self.assertNotEqual(new.snapshot_id, self.old.snapshot_id)


if __name__ == '__main__':
    unittest.main()
