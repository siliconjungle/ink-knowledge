"""Compose universal word deltas for an explicitly bounded group result.

The source result supplies the group domain: each record field is an exact
filtered sum/count. No group labels, unique-row assumptions or trusted metadata
enter the checker. Unbounded dynamic group discovery is a separate tactic.
"""
import copy
from producers.action_replacement import var, cons
from producers.point_delta import sub, match


def setup(model, cache, add, objects, specialized=False):
    reply = cache['case']['normal']['Construct']['arguments'][0]
    if 'Construct' not in reply:
        raise ValueError('grouped aggregate needs a record of word aggregates')
    record = reply['Construct']
    datatype, constructor = record['datatype'], record['constructor']
    fields = objects[datatype]['payload']['declaration']['Datatype']['constructors'][constructor]['fields']
    if not fields or any(field != 'U64' for field in fields):
        raise ValueError('grouped aggregate fields must be u64 totals/counts')
    from producers.aggregate_delta import setup as scalar_setup
    components = []
    for expression in record['arguments']:
        scalar = copy.deepcopy(cache)
        scalar['case']['normal']['Construct']['arguments'][0] = expression
        components.append(scalar_setup(model, scalar, add, objects, specialized=specialized))
    names = ['group_value_' + str(i) for i in range(len(fields))]
    def project(value, index):
        return match(value, [(names, var(names[index]))])
    def make(values):
        return cons(datatype, constructor, values)
    def action(source):
        values = [component['action'](source) for component in components]
        if any(value is None for value in values):
            return None
        return make([sub(value, {'cached_reply': project(var('cached_reply'), i)})
                     for i, value in enumerate(values)])
    def recipe(root, old, bindings):
        return make([component['recipe'](root, project(old, i), bindings)
                     for i, component in enumerate(components)])
    def equality(root, bindings):
        return {'Construct': dict(datatype=datatype, constructor=constructor,
                                 arguments=[component['equality'](root, bindings)
                                            for component in components])}
    return dict(action=action, recipe=recipe, equality=equality, index=0, fused=make([c['fused']for c in components]), fusion_proof=lambda root:{'Construct':dict(datatype=datatype,constructor=constructor,arguments=[c['fusion_proof'](root)for c in components])})
