"""Immutable untrusted search/tuning evidence, outside mathematical discovery."""
from pathlib import Path
from .store import canonical, identity, immutable, read, hash_id
from .cost_models import _decimal, _number


def publish(root, kind, payload, observations=()):
    if kind not in ('observations','models'): raise ValueError('search artifact kind')
    refs=sorted(set(observations))
    if len(refs)>4096: raise ValueError('search provenance budget')
    if kind=='observations' and refs: raise ValueError('observations cannot reference observations')
    if kind=='models' and not refs: raise ValueError('models require observation provenance')
    for ref in refs: load(root,'observations',ref)
    obj=dict(schema=1,semantics='ink-search-'+kind+'-v1',observations=refs,payload=_decimal(payload))
    if len(canonical(obj))>16_000_000: raise ValueError('search artifact byte budget')
    ident=identity(obj);immutable(Path(root)/'store'/'search-artifacts'/kind/(ident+'.json'),obj)
    return ident


def load(root, kind, ident):
    if kind not in ('observations','models'): raise ValueError('search artifact kind')
    obj=read(Path(root)/'store'/'search-artifacts'/kind/(hash_id(ident)+'.json'))
    if identity(obj)!=ident or set(obj)!={'schema','semantics','observations','payload'} or obj['schema']!=1 or obj['semantics']!='ink-search-'+kind+'-v1':
        raise ValueError('search artifact identity/schema')
    refs=obj['observations']
    if not isinstance(refs,list) or len(refs)>4096 or refs!=sorted(set(refs)) or (kind=='observations' and refs):
        raise ValueError('search artifact provenance')
    if kind=='models' and not refs:raise ValueError('model observation provenance required')
    for ref in refs: load(root,'observations',ref)
    return _number(obj['payload'])
