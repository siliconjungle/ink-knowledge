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
    cached=indexed(store)
    if cached is not None:
        return cached
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

# Entry identities are immutable across snapshots; keep their small search keys
# alongside other disposable entry metadata. Snapshot membership remains a join,
# and a selected package still authenticates and replays independently.
TABLE = 'published_bindings_v1'
SCHEMA = '''CREATE TABLE IF NOT EXISTS published_bindings_v1 (
 entry_id TEXT PRIMARY KEY REFERENCES entries(id) ON DELETE CASCADE,
 kind TEXT NOT NULL, binding TEXT);
CREATE INDEX IF NOT EXISTS published_binding_lookup_v1
 ON published_bindings_v1(kind,binding,entry_id);'''


def ensure_schema(db):
    # execute() keeps DDL inside the caller's atomic refresh transaction.
    for statement in SCHEMA.split(';'):
        if statement.strip():
            db.execute(statement)


def insert(db, ident, obj):
    kind = obj['kind']
    if kind not in KINDS:
        return
    payload = obj['payload']
    if kind == 'representation':
        binding = source_key(payload.get('source_objects') or [])
    else:
        package = payload.get('package')
        binding = package.get('input_core_sha256') if isinstance(package, dict) else None
    db.execute('INSERT OR REPLACE INTO published_bindings_v1 VALUES(?,?,?)',
               (ident,kind,binding))


def refresh_missing(store, db):
    """Migrate existing canonical entry summaries once, never per snapshot."""
    missing = [row[0] for row in db.execute('''
      SELECT e.id FROM entries e JOIN members m ON m.entry_id=e.id
      WHERE m.snapshot_id=? AND e.kind IN ('implementation','representation','maintenance')
       AND NOT EXISTS(SELECT 1 FROM published_bindings_v1 b WHERE b.entry_id=e.id)
      ORDER BY e.id''',(store.snapshot_id,))]
    for ident in missing:
        insert(db,ident,store._read_object(ident))
    return len(missing)


def indexed(store):
    """Cheap untrusted filtering, including historical snapshot membership."""
    import sqlite3
    from contextlib import closing
    path = Path(store.root)/'index.sqlite'
    if not path.exists():
        return None
    try:
        with closing(sqlite3.connect(path.as_uri()+'?mode=ro',uri=True)) as db:
            db.execute('BEGIN')
            if not db.execute('SELECT 1 FROM snapshots WHERE id=?',(store.snapshot_id,)).fetchone():
                return None
            missing=db.execute('''SELECT 1 FROM entries e JOIN members m ON m.entry_id=e.id
              WHERE m.snapshot_id=? AND e.kind IN ('implementation','representation','maintenance')
               AND NOT EXISTS(SELECT 1 FROM published_bindings_v1 b WHERE b.entry_id=e.id)
              LIMIT 1''',(store.snapshot_id,)).fetchone()
            if missing:
                return None
            entries = {kind:[] for kind in KINDS}
            for ident,kind,binding in db.execute('''SELECT b.entry_id,b.kind,b.binding
              FROM published_bindings_v1 b JOIN members m ON m.entry_id=b.entry_id
              WHERE m.snapshot_id=? ORDER BY b.entry_id''',(store.snapshot_id,)):
                if kind not in entries or binding is not None and not isinstance(binding,str):
                    return None
                entries[kind].append([ident,binding])
            return entries
    except sqlite3.DatabaseError:
        return None
