"""Pinned, untrusted recipe discovery and complete catalogue coverage.

Recipes live with knowledge. Installed producers author candidates; neither their
names nor catalogue membership grants applicability, equality or profitability.
"""
import argparse, hashlib, importlib, json, re
from collections import Counter
from importlib.resources import files
from pathlib import Path
from .store import canonical, read, KINDS, identity, Store

SEMANTICS='ink-planning-recipes-v1'
MODULE=re.compile(r'producers(?:\.[a-z][a-z0-9_]*)+')

def load(path=None,store=None):
    raw=Path(path).read_bytes() if path else files('ink_knowledge').joinpath('implementation-recipes.json').read_bytes()
    if len(raw)>1_000_000:raise ValueError('recipe registry byte budget')
    registry=json.loads(raw)
    publications=[]
    if store is not None and path is None:
        after=None;published={}
        while True:
            page=store.query(kind='definition',semantics=SEMANTICS,after=after,limit=256)
            for ident in page:
                obj=store.object(ident)
                if set(obj['payload'])!={'recipe'}:raise ValueError('published recipe payload')
                recipe=obj['payload']['recipe'];name=recipe['id']
                if name in published and published[name]!=recipe:raise ValueError('ambiguous published recipe identity')
                published[name]=recipe;publications.append(ident)
            if len(page)<256:break
            after=page[-1]
        registry['recipes']=[r for r in registry['recipes']if r['id']not in published]+list(published.values())
    if set(registry)!={'schema','semantics','recipes'} or registry['schema']!=1 or registry['semantics']!=SEMANTICS:
        raise ValueError('recipe registry schema')
    ids=set()
    for recipe in registry['recipes']:
        if not {'id','module','function','parameters','stage'}<=set(recipe)or set(recipe)-{'id','module','function','parameters','stage','requires','obligations','inputs'}or recipe['id']in ids:
            raise ValueError('recipe fields or duplicate identity')
        if not MODULE.fullmatch(recipe['module']) or not re.fullmatch('[a-z][a-z0-9_]*',recipe['function']):
            raise ValueError('recipes must name installed knowledge producers')
        if recipe['stage'] not in {'rewrite','representation','definitions','properties','physical','routing','resources','migration','extension','maintained','protocol'}:
            raise ValueError('recipe stage')
        if not isinstance(recipe['parameters'],dict):raise ValueError('recipe parameters')
        for field in ['requires','obligations','inputs']:
            if not isinstance(recipe.get(field,[]),list)or any(not isinstance(v,str)or not v for v in recipe.get(field,[])):raise ValueError('recipe '+field)
        ids.add(recipe['id'])
    if len(ids)>4096:raise ValueError('recipe registry count budget')
    return registry,hashlib.sha256(raw).hexdigest()if not publications else identity(dict(resource=hashlib.sha256(raw).hexdigest(),publications=sorted(publications),registry=registry))

def execute(recipe,context):
    missing=[name for name in recipe.get('requires',[])if context.get(name)is None]
    if missing:
        yield dict(status='declined',label=recipe['id'],reason='missing inputs: '+','.join(missing));return
    function=getattr(importlib.import_module(recipe['module']),recipe['function'])
    # A recipe is data selecting a bounded installed producer, never a shell
    # command downloaded from a catalogue entry. Admission happens separately.
    yield from function(context,**recipe['parameters'])

def role(obj):
    kind,sem=obj['kind'],obj['semantics']
    if kind not in KINDS:raise ValueError('unhandled database kind: '+kind)
    if kind=='rewrite' and sem=='ink-conditional-laws-v1':return 'semantic-search'
    if kind=='rewrite' and sem=='ink-general-laws-v1':return 'general-proof-dependency'
    if kind=='representation' and sem in ('ink-source-representation-v1','ink-source-representation-v2'):return 'representation-search'
    if kind=='implementation' and sem=='ink-implementation-candidate-v1':return 'implementation-search'
    if kind=='bridge' and sem=='ink-representation-migration-v1':return 'migration-search'
    if kind in {'definition','theorem'} and sem=='first-order-inductive-equality-v1':
        return 'definition-and-property-search' if kind=='theorem' else 'executable-and-proof-dependency'
    if kind in {'definition','theorem'} and sem=='total-scalar-equality-v1':return 'scalar-proof-dependency'
    if kind=='definition' and sem in {'ink-source-read-capability-v1','ink-source-column-map-v1'}:return 'physical-proof-dependency'
    if kind=='maintenance':return 'maintenance-search'
    if kind=='definition' and sem in {'ink-target-work-measurement-v1','ink-target-work-prices-v1','ink-target-work-publication-context-v1'}:
        return 'cost-evidence'
    if kind=='definition' and sem=='ink-observed-usage-v1':return 'usage-evidence'
    if kind=='definition' and sem==SEMANTICS:return 'recipe-discovery'
    if kind=='definition' and sem=='ink-semantic-producers-v1':return 'semantic-producer-discovery'
    if kind=='definition' and sem=='ink-semantic-law-template-v1':return 'semantic-template-discovery'
    if kind=='definition' and sem=='ink-source-extension-v1':return 'executable-extension'
    if kind=='definition' and sem=='ink-source-algorithm-v1':return 'source-algorithm-discovery'
    raise ValueError('unhandled database semantics: '+kind+'/'+sem)

def coverage(store):
    counts=Counter();operations={};entries={}
    for ident in store.members():
        obj=store.object(ident);handler=role(obj);counts[handler]+=1
        entries[ident]=handler
        for operation in obj['interface']['operations']:
            operations.setdefault(operation,set()).add(handler)
    return dict(schema=1,snapshot=store.snapshot_id,entries=len(entries),roles=dict(sorted(counts.items())),
        operations={k:sorted(v)for k,v in sorted(operations.items())},unhandled=[],
        scope='Discovery coverage; dependencies and evidence are not standalone executable replacements')

def main():
    p=argparse.ArgumentParser();p.add_argument('--registry',type=Path);p.add_argument('--recipe',required=True)
    p.add_argument('--stream',action='store_true');p.add_argument('--context',type=Path,required=True);p.add_argument('-o',type=Path,required=True)
    a=p.parse_args();context=read(a.context)
    root=Path(context['knowledge_root']);snapshot=root/'store/snapshots'/f"{context['knowledge_snapshot']}.json"if context.get('knowledge_snapshot')else None
    registry,digest=load(a.registry,Store(root,snapshot))
    recipe=next(r for r in registry['recipes']if r['id']==a.recipe)
    rows=[];bytes_used=0
    # Streaming preserves already authored proposals if a worker reaches its
    # process budget. Every retained row still needs ordinary kernel admission.
    if a.stream:
        with a.o.open('wb')as output:
            output.write(canonical(dict(recipe=a.recipe,registry_sha256=digest))+b'\n');output.flush()
            for count,result in enumerate(execute(recipe,context)):
                raw=canonical(result);bytes_used+=len(raw)
                if bytes_used>128_000_000 or count>=context.get('candidate_limit',4096):
                    output.write(canonical(dict(status='declined',label='resource budget',reason='recipe candidate or byte budget'))+b'\n');break
                output.write(raw+b'\n');output.flush()
        return
    for result in execute(recipe,context):
        bytes_used+=len(canonical(result))
        if bytes_used>128_000_000:raise ValueError('recipe output byte budget')
        rows.append(result)
        if len(rows)>context.get('candidate_limit',4096):raise ValueError('recipe candidate budget')
    a.o.write_bytes(canonical(dict(recipe=a.recipe,registry_sha256=digest,candidates=rows))+b'\n')

if __name__=='__main__':main()


def indexed_coverage(store):
    """Disposable index diagnostics; never mathematical admission evidence.

    Authenticate the active ID set against its pinned Merkle tree. Indexed kinds,
    semantics and operation labels remain untrusted summaries, like search hints.
    The standalone coverage() audit still authenticates every object body.
    """
    import sqlite3
    from contextlib import closing
    index=store.root/'index.sqlite'
    if not index.exists():return coverage(store)
    counts=Counter();operations={};seen=set()
    with closing(sqlite3.connect(index.as_uri()+'?mode=ro',uri=True))as db:
        if not db.execute('SELECT 1 FROM snapshots WHERE id=?',(store.snapshot_id,)).fetchone():return coverage(store)
        rows=list(db.execute('SELECT e.id,e.kind,e.semantics FROM entries e JOIN members m ON m.entry_id=e.id WHERE m.snapshot_id=?',(store.snapshot_id,)))
        if {r[0]for r in rows}!=set(store.members()):raise ValueError('coverage index membership differs from pinned snapshot')
        handlers={}
        for ident,kind,semantics in rows:
            handler=role(dict(kind=kind,semantics=semantics));counts[handler]+=1;handlers[ident]=handler
        for ident,operation in db.execute('SELECT o.entry_id,o.operation FROM operations o JOIN members m ON m.entry_id=o.entry_id WHERE m.snapshot_id=?',(store.snapshot_id,)):
            operations.setdefault(operation,set()).add(handlers[ident])
    return dict(schema=1,snapshot=store.snapshot_id,entries=len(rows),roles=dict(sorted(counts.items())),operations={k:sorted(v)for k,v in sorted(operations.items())},unhandled=[],scope='Untrusted indexed discovery diagnostics with authenticated active ID set; selected proof closures replay independently; use coverage() for canonical per-object audit')
