"""Publication races exercise real independent processes and canonical files."""
import json
import multiprocessing
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from ink_knowledge import Store, canonical, entry, identity
from ink_knowledge.store import immutable


def extension_writer(root, name, ready, release, attempted, finished, queue, alias_only=False):
    try:
        store = Store(root)
        obj = entry('definition', 'publication-test', {'name': 'seed' if alias_only else name})
        if name == 'first':
            original = Store._publish_ids.__func__
            def delayed(cls, *args):
                ready.set()
                if not release.wait(20):
                    raise RuntimeError('publication test release timeout')
                return original(cls, *args)
            with patch.object(Store, '_publish_ids', classmethod(delayed)):
                result = store.extend([obj], {name: identity(obj)})
        else:
            attempted.set()  # The Store above is pinned before the first commit.
            result = store.extend([obj], {name: identity(obj)})
        queue.put(dict(name=name, status='success', snapshot=result.snapshot_id))
    except Exception as error:
        queue.put(dict(name=name, status='error', error=str(error)))
    finally:
        finished.set()


def immutable_writer(path, value, barrier, queue):
    target = Path(path)
    original = Path.exists
    def simultaneous(candidate):
        present = original(candidate)
        if candidate == target and not present:
            barrier.wait(timeout=20)
        return present
    try:
        # Both creators observe absence before either can publish the file.
        with patch.object(Path, 'exists', simultaneous):
            immutable(target, value)
        queue.put(dict(status='success'))
    except Exception as error:
        queue.put(dict(status='error', error=str(error)))


class PublicationConcurrency(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.context = multiprocessing.get_context('spawn')
        self.processes = []
        self.addCleanup(self.stop_processes)

    def stop_processes(self):
        for process in self.processes:
            if process.is_alive():
                process.terminate()
            process.join(10)

    def start(self, function, *args):
        process = self.context.Process(target=function, args=args)
        process.start()
        self.processes.append(process)
        return process

    def test_conflicting_extensions_cannot_both_report_success_and_lose_members(self):
        seed = entry('definition', 'publication-test', {'name': 'seed'})
        original = Store.publish(self.root, [seed], {'seed': identity(seed)})
        pin = original.data / 'snapshots' / (original.snapshot_id + '.json')
        ready, release, attempted, first_done, second_done = [self.context.Event() for _ in range(5)]
        queue = self.context.Queue()
        first = self.start(extension_writer, self.root, 'first', ready, release,
                           attempted, first_done, queue)
        self.assertTrue(ready.wait(20))
        second = self.start(extension_writer, self.root, 'second', ready, release,
                            attempted, second_done, queue)
        self.assertTrue(attempted.wait(20))
        # With the old implementation the second writer commits during this
        # window. With coordination it waits until the first releases the lock.
        second_done.wait(2)
        release.set()
        outcomes = [queue.get(timeout=30) for _ in range(2)]
        for process in [first, second]:
            process.join(10)
            self.assertEqual(process.exitcode, 0)
        successful = [o for o in outcomes if o['status'] == 'success']
        conflicts = [o for o in outcomes if o['status'] == 'error']
        self.assertEqual([o['name'] for o in successful], ['first'], outcomes)
        self.assertEqual(len(conflicts), 1, outcomes)
        self.assertIn('publication changed during extension', conflicts[0]['error'])
        a = entry('definition', 'publication-test', {'name': 'first'})
        b = entry('definition', 'publication-test', {'name': 'second'})
        current = Store(self.root)
        self.assertEqual(set(current.members()), {identity(seed), identity(a)})
        retried = current.extend([b], {'second': identity(b)})
        self.assertEqual(set(retried.members()), {identity(seed), identity(a), identity(b)})
        self.assertEqual(json.loads((current.data / 'names.json').read_text()),
                         {'seed': identity(seed), 'first': identity(a), 'second': identity(b)})
        historical = Store(self.root, pin)
        self.assertEqual(set(historical.bundle([identity(seed)])['objects']), {identity(seed)})

    def test_names_only_extensions_merge_under_unchanged_snapshot_identity(self):
        seed = entry('definition', 'publication-test', {'name': 'seed'})
        old = Store.publish(self.root, [seed], {'seed': identity(seed)})
        ready, release, attempted, first_done, second_done = [self.context.Event() for _ in range(5)]
        queue = self.context.Queue()
        self.start(extension_writer, self.root, 'first', ready, release,
                   attempted, first_done, queue, True)
        self.assertTrue(ready.wait(20))
        self.start(extension_writer, self.root, 'second', ready, release,
                   attempted, second_done, queue, True)
        self.assertTrue(attempted.wait(20))
        second_done.wait(2)
        release.set()
        outcomes = [queue.get(timeout=30) for _ in range(2)]
        self.assertTrue(all(o['status'] == 'success' for o in outcomes), outcomes)
        self.assertEqual(Store(self.root).snapshot_id, old.snapshot_id)
        self.assertEqual(json.loads((old.data / 'names.json').read_text()),
                         dict.fromkeys(['seed', 'first', 'second'], identity(seed)))

    def test_terminated_writer_releases_lock_and_leaves_previous_snapshot_readable(self):
        seed = entry('definition', 'publication-test', {'name': 'seed'})
        old = Store.publish(self.root, [seed])
        ready, release, attempted, done = [self.context.Event() for _ in range(4)]
        queue = self.context.Queue()
        process = self.start(extension_writer, self.root, 'first', ready, release,
                             attempted, done, queue)
        self.assertTrue(ready.wait(20))
        self.assertEqual(Store(self.root).snapshot_id, old.snapshot_id)
        process.terminate()
        process.join(10)
        self.assertFalse(process.is_alive())
        later = entry('definition', 'publication-test', {'name': 'later'})
        new = Store(self.root).extend([later])
        self.assertEqual(set(new.members()), {identity(seed), identity(later)})
        self.assertEqual(old.object(identity(seed)), seed)

    def immutable_pair(self, same):
        target = self.root / 'object.json'
        first = {'value': 'same'}
        second = first if same else {'value': 'different'}
        barrier = self.context.Barrier(2)
        queue = self.context.Queue()
        processes = [self.start(immutable_writer, str(target), obj, barrier, queue)
                     for obj in [first, second]]
        outcomes = [queue.get(timeout=30) for _ in range(2)]
        for process in processes:
            process.join(10)
            self.assertEqual(process.exitcode, 0)
        self.assertIn(target.read_bytes(), [canonical(first) + b'\n', canonical(second) + b'\n'])
        self.assertEqual(list(self.root.glob('.ink-object-*')), [])
        return outcomes

    def test_io_failure_before_publication_leaves_no_partial_canonical_object(self):
        target = self.root / 'object.json'
        value = {'payload': 'complete bytes'}
        observed = []
        def fail_link(staged, destination):
            self.assertFalse(Path(destination).exists())
            self.assertEqual(Path(staged).read_bytes(), canonical(value) + b'\n')
            observed.append(True)
            raise OSError('injected publication failure')
        with patch('ink_knowledge.store.os.link', side_effect=fail_link):
            with self.assertRaisesRegex(OSError, 'injected publication failure'):
                immutable(target, value)
        self.assertEqual(observed, [True])
        self.assertFalse(target.exists())
        self.assertEqual(list(self.root.glob('.ink-object-*')), [])
        immutable(target, value)
        self.assertEqual(target.read_bytes(), canonical(value) + b'\n')

    def test_identical_immutable_creators_both_succeed(self):
        outcomes = self.immutable_pair(True)
        self.assertTrue(all(o['status'] == 'success' for o in outcomes), outcomes)

    def test_different_immutable_creators_report_collision_without_overwrite(self):
        outcomes = self.immutable_pair(False)
        self.assertEqual(sum(o['status'] == 'success' for o in outcomes), 1)
        rejected = next(o for o in outcomes if o['status'] == 'error')
        self.assertIn('immutable object collision', rejected['error'])


if __name__ == '__main__':
    unittest.main()
