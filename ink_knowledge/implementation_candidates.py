"""Database packaging for checked implementation candidates, without authority.

The package's existing proof protocol determines how it is checked. Names and
membership do not establish equality, applicability, or profitability.
"""
from pathlib import Path
from copy import deepcopy
from .store import Store, entry, identity, hash_id, read

SEMANTICS = 'ink-implementation-candidate-v1'

def proof_views(package):
    """Independent step views retain their own immutable snapshot bindings."""
    if package.get('semantics')=='ink-compiled-plan-v1':
        for step in package['steps']:
            payload=step['package']
            if step['kind']=='definitions':payload=payload['request']
            yield from proof_views(payload)
            if step['kind']=='routing'and payload.get('equivalence'):
                yield payload['equivalence']['knowledge']
    elif 'knowledge'in package:yield package['knowledge']
    refinement=package.get('contract_refinement')
    if refinement:
        for key in ('knowledge','state_knowledge'):
            view=refinement['evidence'].get(key)
            if view:yield view

def identity_selection(source):
    """An ordinary empty selection, represented as data like any other package."""
    hash_id(source)
    return dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=source,
                applications=[], knowledge=dict(schema=1,
                snapshot=dict(schema=1, semantics='ink-knowledge-snapshot-v1',
                              root=identity(dict(schema=1, entries=[]))),
                roots=[], objects={}, membership={}))

def candidate_entry(package, *, shared_knowledge=False):
    roots=sorted({i for view in proof_views(package)for i in view['roots']})
    if shared_knowledge:
        if package.get('semantics')=='ink-compiled-plan-v1':raise ValueError('composed views retain separate snapshot identities')
        package=deepcopy(package)
        del package['knowledge']
        package['knowledge_ref']=dict(schema=1,roots=list(roots))
    return entry('implementation', SEMANTICS, dict(package=package), roots)

def publish_candidates(root, packages, *, shared_knowledge=False):
    """Extend a publication without dropping existing entries or names."""
    root = Path(root)
    objects = {}; names = {}; previous=None
    if (root/'store/snapshot.json').exists():
        previous = Store(root)
        names = read(root/'store/names.json')
    candidates = []
    for package in packages:
        for view in proof_views(package):
            for i, obj in view['objects'].items():
                if identity(obj) != i:
                    raise ValueError('package dependency content mismatch')
                objects[i] = obj
        obj = candidate_entry(package, shared_knowledge=shared_knowledge); i = identity(obj)
        objects[i] = obj; candidates.append(i)
    store = previous.extend(objects.values(), names) if previous is not None else Store.publish(root, objects.values(), names)
    store.ensure_index()
    return store, candidates
