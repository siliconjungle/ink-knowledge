"""Disposable structural discrimination of algorithm and law templates.

Each indexed token is a necessary (not sufficient) condition. Holes and type
parameters are omitted; full binder-aware matching and kernel replay remain.
"""
import sqlite3
from contextlib import closing, nullcontext
from .store import canonical

SEMANTICS = ('ink-semantic-law-template-v1', 'ink-source-algorithm-v1')
SCHEMA = '''CREATE TABLE IF NOT EXISTS template_heads(
 entry_id TEXT PRIMARY KEY REFERENCES entries(id), head TEXT NOT NULL) STRICT;
CREATE INDEX IF NOT EXISTS template_head_lookup ON template_heads(head,entry_id);
CREATE TABLE IF NOT EXISTS template_tokens(
 entry_id TEXT REFERENCES entries(id), path TEXT NOT NULL, token TEXT NOT NULL,
 PRIMARY KEY(entry_id,path)) STRICT;
CREATE INDEX IF NOT EXISTS template_token_lookup ON template_tokens(path,token,entry_id);'''

def tokens(term, params=(), depth=0, path=()):
    from .pattern_index import shape
    from .higher_patterns import applied_hole
    if depth > 4 or applied_hole(term, params): return {}
    head = shape(term, params)
    if head == '*': return {}
    result = {canonical(list(path)).decode(): head}
    # Only Op nodes have the same child topology under higher-order matching.
    node = term['node']
    if isinstance(node,dict) and 'Op' in node:
        for n, child in enumerate(node['Op'][1]):
            result.update(tokens(child,params,depth+1,path+(n,)))
    elif isinstance(node,dict) and 'Lambda' in node:
        result.update(tokens(node['Lambda'],params,depth+1,path+(0,)))
    return result

def insert(db, ident, obj):
    if obj['kind'] != 'definition' or obj['semantics'] not in SEMANTICS:return
    payload=obj['payload'];law=payload.get('law',{})
    if not isinstance(law.get('from'),dict):return
    from .pattern_index import shape
    from .higher_patterns import applied_hole
    params=law.get('params',{})
    db.execute('INSERT OR REPLACE INTO template_heads VALUES(?,?)',
               (ident,'*' if applied_hole(law['from'],params) else shape(law['from'],params)))
    db.executemany('INSERT OR REPLACE INTO template_tokens VALUES(?,?,?)',
                  [(ident,p,t) for p,t in tokens(law['from'],law.get('params',{})).items()])

def refresh(store,db):
    db.executescript(SCHEMA)
    rows=list(db.execute("SELECT e.id FROM entries e JOIN members m ON m.entry_id=e.id LEFT JOIN template_heads t ON t.entry_id=e.id WHERE m.snapshot_id=? AND e.kind='definition' AND e.semantics IN (?,?) AND t.entry_id IS NULL",(store.snapshot_id,*SEMANTICS)))
    for (ident,) in rows:insert(db,ident,store._read_object(ident))

def candidates(store,subject,semantics):
    """Union of potentially applicable templates, sorted and snapshot pinned."""
    from .template_matching import TemplateSites
    sites=TemplateSites(subject)
    index=store.root/'index.sqlite'
    with closing(sqlite3.connect(index.as_uri()+'?mode=ro',uri=True)) if index.exists() else nullcontext(None) as db:
        if db is not None:
            tables={r[0]for r in db.execute("SELECT name FROM sqlite_master WHERE type='table'")}
            if not {'template_heads','template_tokens','snapshots'}<=tables or not db.execute('SELECT 1 FROM snapshots WHERE id=?',(store.snapshot_id,)).fetchone():db=None
        if db is not None:
            db.execute('BEGIN')
            db.execute('CREATE TEMP TABLE subject_tokens(site INTEGER,path TEXT,token TEXT,PRIMARY KEY(site,path))')
            count=0
            for at in range(0,len(sites.sites),256):
                rows=[(i,p,t)for i,(_,_,term)in enumerate(sites.sites[at:at+256],at)for p,t in tokens(term).items()]
                count+=len(rows)
                if count>2_000_000:raise ValueError('template structural token budget')
                db.executemany('INSERT INTO subject_tokens VALUES(?,?,?)',rows)
            db.execute('CREATE INDEX subject_token_lookup ON subject_tokens(path,token,site)')
            # Wildcard roots have no required tokens. Every other template needs
            # one site satisfying ALL its required tokens, not a union of sites.
            sql="""SELECT h.entry_id FROM template_heads h JOIN entries e ON e.id=h.entry_id JOIN members m ON m.entry_id=h.entry_id
 WHERE m.snapshot_id=? AND e.semantics=? AND (h.head='*' OR EXISTS(
 SELECT 1 FROM subject_tokens s WHERE s.path='[]' AND s.token=h.head AND NOT EXISTS(
 SELECT 1 FROM template_tokens t WHERE t.entry_id=h.entry_id AND NOT EXISTS(
 SELECT 1 FROM subject_tokens a WHERE a.site=s.site AND a.path=t.path AND a.token=t.token)))) ORDER BY h.entry_id"""
            return [r[0]for r in db.execute(sql,(store.snapshot_id,semantics))]
    # Old pins and unavailable caches retain complete discovery.
    result=[];after=None
    while True:
        page=store.query(kind='definition',semantics=semantics,after=after,limit=1024)
        result.extend(page)
        if len(page)<1024:return result
        after=page[-1]
