"""Generic typed-head reachability for disposable discovery indexes."""
import json,sqlite3
from contextlib import closing
from .store import canonical
SCHEMA='''CREATE TABLE IF NOT EXISTS pattern_roots(entry_id TEXT PRIMARY KEY REFERENCES entries(id),sort TEXT NOT NULL,head TEXT NOT NULL) STRICT;
CREATE INDEX IF NOT EXISTS pattern_root_lookup ON pattern_roots(sort,head,entry_id);
CREATE TABLE IF NOT EXISTS pattern_targets(entry_id TEXT REFERENCES entries(id),sort TEXT NOT NULL,head TEXT NOT NULL,PRIMARY KEY(entry_id,sort,head)) STRICT;'''

def shape(term,params=()):
    node=term['node']
    if isinstance(node,dict):
        if 'Free'in node and node['Free']in params:return '*'
        if 'Op'in node:return 'Op:'+node['Op'][0]
        return next(iter(node))
    return str(node)


class TermIndex:
    """Disposable head buckets with exact sort filtering and stable term order.

    A root formal can match any term of its sort. Other roots can only match
    the same constructor/operator. Callers must still run their exact matcher
    and ordinary proof admission; bucket membership supplies no facts. Rebuild
    when the subject changes; no mutable subject state is cached across calls.
    """
    def __init__(self, terms):
        self.terms = tuple(terms)
        self.roots = {}
        for term in self.terms:
            self.roots.setdefault(shape(term), []).append(term)

    def candidates(self, pattern, params=()):
        head = shape(pattern, params)
        terms = self.terms if head == '*' else self.roots.get(head, ())
        return (term for term in terms if term['sort'] == pattern['sort'])

def heads(term):
    result=set()
    def visit(t):
        if isinstance(t,dict):
            if 'sort'in t and 'node'in t:result.add((canonical(t['sort']).decode(),shape(t)))
            for v in t.values():visit(v)
        elif isinstance(t,list):
            for v in t:visit(v)
    visit(term);return result

def insert(db,ident,obj):
    if obj['kind']!='rewrite' or obj['semantics']!='ink-conditional-laws-v1':return
    p=obj['payload'];source=p.get('from');target=p.get('to')
    if not isinstance(source,dict)or not {'sort','node'}<=set(source)or not isinstance(target,dict):return
    db.execute('INSERT OR REPLACE INTO pattern_roots VALUES(?,?,?)',(ident,canonical(source['sort']).decode(),shape(source,p.get('params',{}))))
    db.executemany('INSERT OR IGNORE INTO pattern_targets VALUES(?,?,?)',[(ident,s,h)for s,h in sorted(heads(target))])

def refresh(store,db,*,schema_ready=False):
    if not schema_ready:db.executescript(SCHEMA)
    # This is a one-time migration for older disposable indexes, plus newly
    # published semantic laws. Authentic object bytes supply metadata; selected
    # mathematical dependency closures still replay independently.
    missing=[r[0]for r in db.execute("SELECT e.id FROM entries e WHERE e.kind='rewrite' AND e.semantics='ink-conditional-laws-v1' AND NOT EXISTS(SELECT 1 FROM pattern_roots p WHERE p.entry_id=e.id) AND EXISTS(SELECT 1 FROM members m WHERE m.entry_id=e.id AND m.snapshot_id=?)",(store.snapshot_id,))]
    for ident in missing:insert(db,ident,store._read_object(ident))

def candidates(store,sort,head,after=None,limit=1024):
    if not isinstance(limit,int) or not 0<=limit<=1024:raise ValueError('query limit')
    index=store.root/'index.sqlite';sort=canonical(sort).decode()
    if index.exists():
        with closing(sqlite3.connect(index.as_uri()+'?mode=ro',uri=True))as db:
            if db.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='pattern_roots'").fetchone()and db.execute('SELECT 1 FROM snapshots WHERE id=?',(store.snapshot_id,)).fetchone():
                sql='SELECT p.entry_id FROM pattern_roots p JOIN members m ON m.entry_id=p.entry_id WHERE m.snapshot_id=? AND p.sort=? AND p.head IN (?,?)';args=[store.snapshot_id,sort,head,'*']
                if after is not None:sql+=' AND p.entry_id>?';args.append(after)
                return [r[0]for r in db.execute(sql+' ORDER BY p.entry_id LIMIT ?',args+[limit])]
    # Conservative fallback preserves discovery on old/no-index publications.
    # Its extra candidates still need normal pattern matching and proof replay.
    return store.query(kind='rewrite',semantics='ink-conditional-laws-v1',result=json.loads(sort),after=after,limit=limit)

def targets(store,ident):
    index=store.root/'index.sqlite'
    if index.exists():
        with closing(sqlite3.connect(index.as_uri()+'?mode=ro',uri=True))as db:
            if db.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='pattern_targets'").fetchone():
                found=list(db.execute('SELECT sort,head FROM pattern_targets WHERE entry_id=?',(ident,)))
                if found:return set(found)
    return heads(store.object(ident)['payload']['to'])


class Reader:
    """One read connection per reachability walk; metadata is never authority."""
    def __init__(self,store):
        self.store=store;self.db=None
    def __enter__(self):
        index=self.store.root/'index.sqlite'
        if index.exists():
            db=sqlite3.connect(index.as_uri()+'?mode=ro',uri=True)
            try:
                tables={r[0]for r in db.execute("SELECT name FROM sqlite_master WHERE type='table'")}
                if {'pattern_roots','pattern_targets','snapshots'}<=tables and db.execute('SELECT 1 FROM snapshots WHERE id=?',(self.store.snapshot_id,)).fetchone():
                    self.db=db
                else:db.close()
            except BaseException:
                db.close()
                raise
        return self
    def __exit__(self,*_):
        db,self.db=self.db,None
        if db is not None:db.close()
    def candidates(self,sort,head,after=None,limit=1024):
        if not isinstance(limit,int) or not 0<=limit<=1024:raise ValueError('query limit')
        if self.db is None:return candidates(self.store,sort,head,after,limit)
        sql='SELECT p.entry_id FROM pattern_roots p JOIN members m ON m.entry_id=p.entry_id WHERE m.snapshot_id=? AND p.sort=? AND p.head IN (?,?)'
        args=[self.store.snapshot_id,canonical(sort).decode(),head,'*']
        if after is not None:sql+=' AND p.entry_id>?';args.append(after)
        return [r[0]for r in self.db.execute(sql+' ORDER BY p.entry_id LIMIT ?',args+[limit])]
    def targets(self,idents):
        ids=sorted(set(idents));result=set();found=set()
        if self.db is not None:
            for at in range(0,len(ids),256):
                batch=ids[at:at+256]
                for ident,sort,head in self.db.execute('SELECT entry_id,sort,head FROM pattern_targets WHERE entry_id IN ('+','.join('?'for _ in batch)+')',batch):
                    found.add(ident);result.add((sort,head))
        for ident in set(ids)-found:result.update(heads(self.store.object(ident)['payload']['to']))
        return result
