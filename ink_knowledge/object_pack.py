"""Optional packed transport for canonical objects; bytes still authenticate.

The pack is a disposable read-only SQLite container, not a proof cache. Loose
objects take precedence so corruption of an existing canonical file is visible.
"""
import os, sqlite3, tempfile
from contextlib import closing, contextmanager, nullcontext
from pathlib import Path
from .store import canonical, hash_id, MAX_VIEW_BYTES

@contextmanager
def reader(store):
    path=store.data/'objects.pack.sqlite'
    with closing(sqlite3.connect(path.as_uri()+'?mode=ro',uri=True)) if path.exists() else nullcontext(None) as db:
        if db is not None:db.execute('BEGIN')
        yield db

def read(store,ident,db=None):
    hash_id(ident)
    loose=store.data/'objects'/f'{ident}.json'
    from .store import _read_canonical
    try:
        return _read_canonical(loose)
    except FileNotFoundError:pass
    if db is None:
        with reader(store) as connection:
            if connection is None:raise FileNotFoundError(loose)
            return read(store,ident,connection)
    row=db.execute('SELECT bytes FROM objects WHERE id=?',(ident,)).fetchone()
    if row is None:raise FileNotFoundError(loose)
    raw=row[0]
    if not isinstance(raw,bytes)or len(raw)>MAX_VIEW_BYTES:raise ValueError('packed object byte limit')
    import json
    value=json.loads(raw);encoded=canonical(value)
    if raw!=encoded:raise ValueError('noncanonical packed object')
    return value,encoded

def pack(store):
    """Atomically extend a transport pack; do not remove canonical Git files."""
    path=store.data/'objects.pack.sqlite';fd,tmp=tempfile.mkstemp(prefix='.ink-pack-',dir=store.data);os.close(fd)
    count=0;total=0
    try:
        with reader(store)as prior,closing(sqlite3.connect(tmp))as db:
            if prior is not None:prior.backup(db)
            db.execute('CREATE TABLE IF NOT EXISTS objects(id TEXT PRIMARY KEY,bytes BLOB NOT NULL) WITHOUT ROWID')
            with db:
                for ident in store.members():
                    obj=store._read_object(ident,prior);raw=canonical(obj)
                    db.execute('INSERT OR REPLACE INTO objects VALUES(?,?)',(ident,raw));count+=1;total+=len(raw)
            db.execute('VACUUM')
        os.replace(tmp,path)
    finally:
        if Path(tmp).exists():Path(tmp).unlink()
    return dict(snapshot=store.snapshot_id,objects=count,canonical_bytes=total,pack_bytes=path.stat().st_size)
