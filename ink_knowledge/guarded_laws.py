"""Guarded variants of conditional laws: data-dependent premises become path facts.

A conditional law `from == to` with Bool premises `c_i == b_i` applies only
where the checker can establish every premise. When a premise depends on data
(a callback's item, a field of a record argument) it holds at some calls and
not others, so no site proof exists and the law is a near miss.

Its guarded variant has no premises:

    from == choose(c_1, choose(c_2, to, from), from)      (b_1 = b_2 = true)

The checked proof splits on each condition. In the branch where every premise
holds it uses the original law with the branch hypotheses as premise proofs;
elsewhere both sides normalise to `from`. The variant is a law like any other:
it grants no authority until the kernel checks it with its dependency, and a
guarded program is an ordinary alternative that measurement or a validated
work model must still prefer. The runtime test is the price; whether the
specialised branch repays it is an empirical question, never assumed here.
"""
import copy

from .store import identity, semantic_entry

CONDITIONAL = 'ink-conditional-laws-v1'
MAX_CONDITIONS = 3
BOOL = {'Value': 'Bool'}


def _choose(condition, on_true, on_false):
    return dict(sort=on_true['sort'], node={'Op': ['call:choose', [condition, on_true, on_false]]})


def _mentions_parameter(term, params):
    node = term.get('node') if isinstance(term, dict) else None
    if isinstance(node, dict):
        if 'Free' in node:
            return node['Free'] in params
        return any(_mentions_parameter(v, params) for v in node.values())
    if isinstance(node, list):
        return any(_mentions_parameter(v, params) for v in node)
    if isinstance(term, list):
        return any(_mentions_parameter(v, params) for v in term)
    return False


def eligible(entry):
    """Concrete rewrite laws whose premises are Bool tests on their parameters."""
    if entry.get('kind') != 'rewrite' or entry.get('semantics') != CONDITIONAL:
        return False
    law = entry['payload']
    conditions = law.get('conditions') or []
    if not 1 <= len(conditions) <= MAX_CONDITIONS or law.get('types') or law.get('assumptions'):
        return False
    for c in conditions:
        if c['from'].get('sort') != BOOL or c['to'] not in (dict(sort=BOOL, node={'Bool': True}), dict(sort=BOOL, node={'Bool': False})):
            return False
    # A premise over constants alone is decided once; only data-dependent
    # premises benefit from a runtime test.
    return any(_mentions_parameter(c['from'], law['params']) for c in conditions)


def guard(ident, entry):
    """The guarded variant of one eligible conditional law, as a store entry."""
    law = entry['payload']
    conditions = law['conditions']
    original, specialised = law['from'], law['to']
    to = specialised
    for c in reversed(conditions):
        holds = c['to']['node']['Bool']
        to = _choose(c['from'], to, original) if holds else _choose(c['from'], original, to)
    arguments = {name: dict(sort=sort, node={'Free': name}) for name, sort in sorted(law['params'].items())}
    use = {'Use': dict(law=ident, arguments=arguments, premises=[{'Hypothesis': i} for i in range(len(conditions))])}
    applied = {'Trans': dict(middle=copy.deepcopy(specialised), left=use, right='Normalize')}

    def split(index):
        # Cases appends each branch hypothesis in order, so at the leaf where
        # every premise holds hypothesis i is exactly the law's condition i.
        if index == len(conditions):
            return applied
        holds = conditions[index]['to']['node']['Bool']
        matching, other = split(index + 1), 'Normalize'
        return {'Cases': dict(condition=conditions[index]['from'],
                              on_true=matching if holds else other,
                              on_false=other if holds else matching)}

    guarded = dict(schema=1, semantics=CONDITIONAL, params=law['params'], conditions=[],
                   proof=split(0), dependencies=sorted({ident}), **{'from': original, 'to': to})
    return semantic_entry(guarded)


def generate(objects):
    """Guarded entries for every eligible law among `objects` (ident -> entry)."""
    out = {}
    for ident, entry in sorted(objects.items()):
        if eligible(entry):
            derived = guard(ident, entry)
            out[identity(derived)] = derived
    return out


def guard_condition(law):
    """The outermost test of a guarded law's right side, or None."""
    node = law['to']['node']
    if isinstance(node, dict) and node.get('Op', [None])[0] == 'call:choose':
        return node['Op'][1][0]
    return None
