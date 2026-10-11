"""General collection-edit identities, proved by quantified structural induction.

Private owned storage has extensional value semantics. These laws say nothing
about transaction order, events, replication protocols or persistence.
"""
import json

from producers.semantic_laws import value, term, var, word, op, law

CARRIERS = ('U32', 'U64', 'I32', 'F32', 'Bool', 'String', 'Int', 'Unit')


def carrier_laws(t):
    scalar, sequence, buffer = value(t), value({'List': t}), value({'Buffer': t})
    xs, i = var(sequence, 'xs'), var(value('U32'), 'i')
    a, b = var(scalar, 'a'), var(scalar, 'b')

    def owner(xs): return op(buffer, 'call:buffer', xs)
    def freeze(b): return op(sequence, 'method:freeze', b)
    def write(b, i, x): return op(buffer, 'method:set', b, i, x)
    def cut(b, i): return op(buffer, 'method:truncate', b, i)
    def cons(h, tail): return term(sequence, {'Cons': [h, tail]})

    endpoints = {
        'overwrite': (lambda xs, i: freeze(write(write(owner(xs), i, a), i, b)),
                      lambda xs, i: freeze(write(owner(xs), i, b)),
                      dict(xs=sequence, i=value('U32'), a=scalar, b=scalar)),
        'unchanged-write': (lambda xs, i: freeze(write(owner(xs), i, op(scalar, 'method:at_or', xs, i, a))),
                            lambda xs, i: xs,
                            dict(xs=sequence, i=value('U32'), a=scalar)),
        'truncate-idempotent': (lambda xs, i: freeze(cut(cut(owner(xs), i), i)),
                                lambda xs, i: freeze(cut(owner(xs), i)),
                                dict(xs=sequence, i=value('U32'))),
    }
    rows = []
    head, tail = var(scalar, 'head'), var(sequence, 'tail')
    dec = op(value('U32'), 'binary:-', i, word('U32', 1))
    condition = op(value('Bool'), 'binary:==', i, word('U32', 0))
    for name, (source, target, params) in endpoints.items():
        # Expose one constructor on both sides, then instantiate the induction
        # hypothesis at i-1 on the immediate tail. Nothing assumes an index bound.
        left, right = cons(head, source(tail, dec)), cons(head, target(tail, dec))
        recursive = {'Trans': dict(middle=left, left='Normalize', right={
            'Trans': dict(middle=right, left={'Congruence': [
                'Normalize', {'GeneralizedHypothesis': dict(index=0, arguments={'i': dec})}
            ]}, right='Normalize')})}
        proof = {'GeneralizedInduction': dict(variable='xs', generalize=['i'],
            names=['head', 'tail'], base='Normalize', step={'Cases': dict(
                condition=condition, on_false=recursive, on_true='Normalize')})}
        rows.append((f'collection-edit/{name}-{str(t).lower()}', law(params, source(xs, i), target(xs, i), proof)))
    return rows


def named_laws():
    return [row for t in CARRIERS for row in carrier_laws(t)]


def specialize(subject, core=None):
    """The same theorem for admitted structural and nominal element carriers."""
    from ink_planner.semantic_search import positions
    carriers = {}
    for root in subject['functions'].values():
        for _, node in positions(root):
            sort = node['sort']
            ty = sort.get('Value') if isinstance(sort, dict) else None
            if isinstance(ty, dict) and ('List' in ty or 'Buffer' in ty):
                t = ty.get('List', ty.get('Buffer'))
                carriers[json.dumps(t, sort_keys=True)] = t
    return [row for key in sorted(carriers) for row in carrier_laws(carriers[key])][:256]
