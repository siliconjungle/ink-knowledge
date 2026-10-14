"""Atomic selection of snapshot and aliases; neither grants proof authority.

The two legacy metadata files are recoverable mirrors. Readers select one small
record and authenticate its immutable name map. This is process-interruption
recovery, not a promise of durability across power loss (no fsync protocol).
"""
import os
import tempfile
from pathlib import Path
from .store import canonical, fields, hash_id, identity, immutable, read, SNAPSHOT

SEMANTICS = 'ink-knowledge-publication-v1'


def validate_names(names):
    if not isinstance(names, dict) or any(not isinstance(k, str) for k in names):
        raise ValueError('invalid publication names')
    for value in names.values():
        hash_id(value)
    return names


def generation(snapshot, names):
    return dict(schema=1, semantics=SEMANTICS, snapshot=snapshot,
                names=identity(validate_names(names)))


def validate(value):
    fields(value, ('schema', 'semantics', 'snapshot', 'names'))
    if type(value['schema']) is not int or value['schema'] != 1 or value['semantics'] != SEMANTICS:
        raise ValueError('unsupported publication')
    hash_id(value['names'])
    snapshot = value['snapshot']
    if snapshot is not None:
        fields(snapshot, ('schema', 'semantics', 'root'))
        if type(snapshot['schema']) is not int or snapshot['schema'] != 1 or snapshot['semantics'] != SNAPSHOT:
            raise ValueError('unsupported snapshot')
        hash_id(snapshot['root'])
    return value


def capture(data):
    """Capture a generation without taking the writer lock.

    Before the first coordinated publication, capture the legacy pair and then
    recheck the selector. Bootstrap always precedes either mirror mutation.
    An invalid selector is an error, never a reason to trust the mirrors.
    """
    pointer = data / 'publication.json'
    try:
        return validate(read(pointer)), None
    except FileNotFoundError:
        pass
    error = None
    try:
        try:
            snapshot = read(data / 'snapshot.json')
        except FileNotFoundError:
            snapshot = None
        try:
            names = read(data / 'names.json') if snapshot is not None else {}
        except FileNotFoundError:
            names = {}
        legacy = validate(generation(snapshot, names))
    except (OSError, ValueError) as failure:
        error = failure
    try:
        return validate(read(pointer)), None
    except FileNotFoundError:
        if error is not None:
            raise error
        return legacy, names


def load_names(data, selected, cached=None):
    names = cached if cached is not None else read(data / 'names' / (selected['names'] + '.json'))
    validate_names(names)
    if identity(names) != selected['names']:
        raise ValueError('publication names content mismatch')
    return names


def replace(path, value):
    data = canonical(value) + b'\n'
    fd, temporary = tempfile.mkstemp(prefix='.ink-pointer-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(data)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def repair(data, selected, names):
    for name, value in [('names.json', names), ('snapshot.json', selected['snapshot'])]:
        path = data / name
        if value is None:
            path.unlink(missing_ok=True)
            continue
        try:
            actual = read(path)
        except (OSError, ValueError):
            actual = None
        if actual != value:
            replace(path, value)


def commit(data, snapshot, names):
    """Publish while the caller holds Store's stable publication lock."""
    names = validate_names(names)
    new = validate(generation(snapshot, names))
    old, cached = capture(data)
    old_names = load_names(data, old, cached)
    immutable(data / 'names' / (old['names'] + '.json'), old_names)
    immutable(data / 'names' / (new['names'] + '.json'), names)
    pointer = data / 'publication.json'
    if not pointer.exists():
        replace(pointer, old)
    repair(data, old, old_names)
    try:
        replace(data / 'names.json', names)
        replace(data / 'snapshot.json', snapshot)
        replace(pointer, new)  # The single commit point.
    except BaseException:
        try:
            repair(data, old, old_names)
        except OSError:
            pass  # The selector still protects readers if mirrors cannot recover.
        raise
