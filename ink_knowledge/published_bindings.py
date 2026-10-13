"""Disposable per-snapshot index of what each published package is bound to.

Planning asks, at every admitted state, which published implementations,
representations and maintenance packages belong to the current source. Loading
every package body to answer that dominated the recipe's time. This sidecar
records each entry's binding once per snapshot: an implementation or maintenance
package's input core, or a representation's source objects. It is a search
filter only. A wrong or stale file can hide or suggest a proposal, never admit
one: every proposal is still checked against the exact module, and the file is
rebuilt whenever the pinned snapshot differs.
"""
import hashlib, json, os, tempfile
from pathlib import Path

NAME = 'index-published.json'
KINDS = ('implementation', 'representation', 'maintenance')


def source_key(source_objects):
    return hashlib.sha256(json.dumps(sorted(source_objects), separators=(',', ':')).encode()).hexdigest()


def build(store):
    entries = {kind: [] for kind in KINDS}
    for kind in KINDS:
        after = None
        while True:
            page = store.query(kind=kind, after=after, limit=256)
            for ident in page:
                payload = store.object(ident)['payload']
                if kind == 'representation':
                    binding = source_key(payload.get('source_objects') or [])
                else:
                    package = payload.get('package')
                    binding = package.get('input_core_sha256') if isinstance(package, dict) else None
                entries[kind].append([ident, binding])
            if len(page) < 256:
                break
            after = page[-1]
    return dict(schema=1, snapshot=store.snapshot_id, entries=entries)


def bindings(store):
    path = Path(store.root) / NAME
    try:
        value = json.loads(path.read_text())
        if value.get('schema') == 1 and value.get('snapshot') == store.snapshot_id:
            return value['entries']
    except (OSError, ValueError, AttributeError):
        pass
    value = build(store)
    try:
        fd, temporary = tempfile.mkstemp(prefix='.ink-published-', dir=store.root)
        with os.fdopen(fd, 'w') as stream:
            json.dump(value, stream, separators=(',', ':'))
        os.replace(temporary, path)
    except OSError:
        pass
    return value['entries']
