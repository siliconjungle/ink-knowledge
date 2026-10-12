"""Exact family attribution of observations; no inferred profitability.

Family IDs must be recorded explicitly in each observation's entries. Absence
of that attribution remains unknown, rather than guessed from a program name.
"""
import sqlite3
from contextlib import closing
from .store import canonical,identity,read,hash_id

SCHEMA='''CREATE TABLE IF NOT EXISTS observation_entries(
 observation_id TEXT REFERENCES observations(id), entry_id TEXT NOT NULL,
 PRIMARY KEY(observation_id,entry_id)) STRICT;
CREATE INDEX IF NOT EXISTS observation_entry_lookup ON observation_entries(entry_id,observation_id);
CREATE TABLE IF NOT EXISTS observation_attribution(id TEXT PRIMARY KEY REFERENCES observations(id)) STRICT;'''

def insert(db,ident,obj):
    db.executemany('INSERT OR IGNORE INTO observation_entries VALUES(?,?)',[(ident,i)for i in obj['entries']])
    db.execute('INSERT OR IGNORE INTO observation_attribution VALUES(?)',(ident,))

def refresh(store,db):
    db.executescript(SCHEMA)
    # Empty attribution is valid, so record migration completion explicitly.
    db.execute('CREATE TABLE IF NOT EXISTS observation_attribution(id TEXT PRIMARY KEY REFERENCES observations(id)) STRICT')
    for (ident,)in list(db.execute('SELECT id FROM observations WHERE id NOT IN (SELECT id FROM observation_attribution)')):
        obj=read(store.data/'observations'/f'{hash_id(ident)}.json');store.validate_observation(obj)
        if identity(obj)!=ident:raise ValueError('observation content mismatch')
        insert(db,ident,obj)

def page(store,families,target,workload,after=None,limit=1024):
    ids=sorted(set(families))
    if len(ids)>1024 or type(limit)is not int or not 0<=limit<=1024:raise ValueError('family evidence budget')
    for i in ids:hash_id(i)
    if after is not None:hash_id(after)
    if not ids or limit==0:return []
    store.ensure_index()
    with closing(sqlite3.connect((store.root/'index.sqlite').as_uri()+'?mode=ro',uri=True))as db:
        # An older cache may not yet have the attribution projection.
        ready=db.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='observation_entries'").fetchone()
    if not ready:store.refresh_index()
    result=[];cursor=after
    with closing(sqlite3.connect((store.root/'index.sqlite').as_uri()+'?mode=ro',uri=True))as db:
        while len(result)<limit:
            sql='SELECT DISTINCT o.id FROM observations o JOIN observation_entries f ON f.observation_id=o.id WHERE f.entry_id IN ('+','.join('?'for _ in ids)+') AND o.target=? AND o.workload=?'
            args=[*ids,canonical(target).decode(),canonical(workload).decode()]
            if cursor is not None:sql+=' AND o.id>?';args.append(cursor)
            candidates=[r[0]for r in db.execute(sql+' ORDER BY o.id LIMIT ?',args+[limit-len(result)])]
            if not candidates:break
            for ident in candidates:
                obj=read(store.data/'observations'/f'{hash_id(ident)}.json');store.validate_observation(obj)
                if identity(obj)!=ident:raise ValueError('observation content mismatch')
                if set(ids)&set(obj['entries'])and obj['target']==target and obj['workload']==workload:result.append(obj)
            cursor=candidates[-1]
    return result
