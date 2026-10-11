"""Immutable profitability models, separate from mathematical knowledge authority."""
import json,math
from importlib.resources import files
from .store import Store,canonical,identity,immutable,read,hash_id


def structural_prices():
    return json.loads(files('ink_knowledge').joinpath('structural-costs.json').read_text())['operation_costs']


def structural_components():
    """Unmeasured search diversity metadata, never mathematical knowledge."""
    return json.loads(files('ink_knowledge').joinpath('structural-costs.json').read_text()).get('search_components', {})


def _decimal(v):
    if isinstance(v,float):
        if not math.isfinite(v):raise ValueError('nonfinite model price')
        return {'decimal':format(v,'.17g')}
    if isinstance(v,dict):return {k:_decimal(x)for k,x in v.items()}
    if isinstance(v,list):return [_decimal(x)for x in v]
    return v


def _number(v):
    if isinstance(v,dict)and set(v)=={'decimal'}:return float(v['decimal'])
    if isinstance(v,dict):return {k:_number(x)for k,x in v.items()}
    if isinstance(v,list):return [_number(x)for x in v]
    return v


def publish_model(store,profile,observations):
    """A model has no proof kind and cannot enter checker discovery."""
    refs=sorted(set(observations))
    if not refs or len(refs)>4096:raise ValueError('models require bounded observation provenance')
    for id in refs:
        obj=read(store.data/'observations'/f'{hash_id(id)}.json');Store.validate_observation(obj)
        if identity(obj)!=id:raise ValueError('observation hash mismatch')
    value=dict(schema=1,semantics='ink-cost-model-v1',observations=refs,profile=_decimal(profile))
    id=identity(value);immutable(store.data/'cost-models'/f'{id}.json',value);return id


def load_model(store,id):
    value=read(store.data/'cost-models'/f'{hash_id(id)}.json')
    if identity(value)!=id or value.get('schema')!=1 or value.get('semantics')!='ink-cost-model-v1':raise ValueError('invalid cost model')
    for ref in value['observations']:
        o=read(store.data/'observations'/f'{hash_id(ref)}.json');Store.validate_observation(o)
        if identity(o)!=ref:raise ValueError('observation hash mismatch')
    return _number(value['profile'])
