"""Bounded, normalized disposable membership cache; canonical trees unchanged."""
from .store import canonical,identity
import time
MAX_SNAPSHOTS=16
TABLES=('entries','dependencies','types','operations','effects','applicability','names','observations')

def copy(source,target,db):
    columns={r[1]for r in source.execute('PRAGMA table_info(members)')}
    if 'witness_id'in columns:
        source.backup(db);return
    # Reuse untrusted discovery summaries, not duplicated old witness blobs.
    # Recreate membership from the authenticated current canonical tree below.
    from pathlib import Path
    db.executescript(Path(__file__).with_name('index.sql').read_text())
    db.execute('ATTACH DATABASE ? AS legacy',(target.as_uri()+'?mode=ro',))
    with db:
        for table in TABLES:db.execute(f'INSERT INTO {table} SELECT * FROM legacy.{table}')
    db.execute('DETACH DATABASE legacy')

def member(db,snapshot,ident,witness,cache):
    key=tuple(witness['entries'])
    if key not in cache:
        payload=canonical(witness).decode();wid=identity(witness)
        db.execute('INSERT OR IGNORE INTO witnesses VALUES(?,?)',(wid,payload));cache[key]=wid
    db.execute('INSERT OR REPLACE INTO members VALUES(?,?,?)',(snapshot,ident,cache[key]))

def prune(db,snapshot):
    db.execute('UPDATE snapshots SET touched=? WHERE id=?',(time.time_ns(),snapshot))
    stale=[r[0]for r in db.execute('SELECT id FROM snapshots ORDER BY touched DESC,id LIMIT -1 OFFSET ?',(MAX_SNAPSHOTS,))]
    for ident in stale:
        db.execute('DELETE FROM members WHERE snapshot_id=?',(ident,));db.execute('DELETE FROM snapshots WHERE id=?',(ident,))
    db.execute('DELETE FROM witnesses WHERE NOT EXISTS(SELECT 1 FROM members m WHERE m.witness_id=witnesses.id)')
