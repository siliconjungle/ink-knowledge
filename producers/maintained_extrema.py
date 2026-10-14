"""Untrusted authoring of word maximum/minimum keeps as maintained extremum views.

A keep whose per-row unfolding over its table is a word maximum (identity 0)
or minimum (identity 2^64-1) becomes an `ink-maintained-fold-v1` view with an
`extremum`: the core checks the exact source factorisation, that `combine` is
the fixed word max/min with its identity, associativity and commutativity, and
insertion; the fixed controller keeps the multiset of contributions. Every word
fact is a bit-vector certificate the kernel replays. Shapes that do not unfold
this way decline.
"""
import json
from producers.action_replacement import var, call, cons, convert, trans
from producers.point_delta import binary, normal, sub, replace

MAX_WORD = 2 ** 64 - 1
WORD_OPS = {'<', '>', '<=', '>=', '==', '!=', '+', '-', '*', '&'}


def _if(condition, on_true, on_false):
    return {'If': dict(condition=condition, on_true=on_true, on_false=on_false)}


def abstract(terms):
    """Replace maximal non-word subterms by shared variables (in first-seen
    order) so a bit-vector certificate can state the remaining word fact."""
    opaque = []

    def walk(t):
        if isinstance(t, dict):
            if 'U64' in t or 'Bool' in t:
                return t
            if 'Binary' in t and t['Binary']['op'] in WORD_OPS:
                x = t['Binary']
                return binary(x['op'], walk(x['left']), walk(x['right']))
            if 'If' in t:
                x = t['If']
                return _if(walk(x['condition']), walk(x['on_true']), walk(x['on_false']))
        if t not in opaque:
            opaque.append(t)
        return var('extremum_word_' + str(opaque.index(t)))
    return [walk(t) for t in terms], opaque


def author(subject, model, objects, add, compiler, certificates):
    """One extremum view for `subject`, or raise ValueError to decline."""
    from producers.sorted_rows import word_certificate
    if subject['result'] != 'U64' or subject['key'] != 'U64':
        raise ValueError('extremum views author word results over word keys')
    rows = subject['rows']
    binding = subject['bindings'][subject['root']]
    query = subject['value']
    q = lambda r: sub(query, {binding: r})
    nil = cons(rows, 0, [])
    zero = normal(q(nil), objects)
    if zero == {'U64': 0}:
        order = 'max'
    elif zero == {'U64': MAX_WORD}:
        order = 'min'
    else:
        raise ValueError('keep over an empty table is not a word max/min identity')
    a, b = var('a'), var('b')
    less = binary('<', a, b)
    body = _if(less, b, a) if order == 'max' else _if(less, a, b)
    combine = add({'Function': dict(params=[['a', 'U64'], ['b', 'U64']], result='U64', body=body, recursive=None)})
    key, row, tail = var('key'), var('row'), var('tail')
    contribution_body = normal(q(cons(rows, 1, [key, row, nil])), objects)
    contribution = add({'Function': dict(params=[['key', subject['key']], ['row', subject['row']]], result='U64',
                                         body=contribution_body, recursive=None)})
    c = lambda x, y: call(combine, [x, y])
    contrib = lambda r: call(contribution, [key, r])

    # The core's fixed fold meaning (core/src/maintained.rs `fold`), with its
    # exact dependency set.
    from ink_knowledge.store import entry
    from ink_knowledge import identity
    from producers.representations import match
    payload = dict(declaration={'Function': dict(params=[['rows', {'Data': rows}]], result='U64', recursive=0, body=match(var('rows'), [
        ([], zero), (['key', 'row', 'tail'], c(contrib(row), {'SelfCall': [tail]}))]))})
    exact = entry('definition', 'first-order-inductive-equality-v1', payload, sorted({rows, contribution, combine}),
                  parameters={'rows': {'Data': rows}}, result='U64')
    fold = identity(exact)
    objects[fold] = exact
    total = lambda r: call(fold, [r])

    def word_fact(left, right, params):
        """Proof of `left = right` for word terms: normalise both sides, then a
        certificate for the abstracted word identity, instantiated by Use."""
        nl, nr = normal(left, objects), normal(right, objects)
        if nl == nr:
            return convert(left, right)
        (al, ar), opaque = abstract([nl, nr])
        names = [[f'extremum_word_{i}', 'U64'] for i in range(len(opaque))]
        goal = dict(params=names, conditions=[], **{'from': al, 'to': ar})
        cert = word_certificate(compiler, goal, certificates)
        theorem = add({'Theorem': dict(**goal, proof={'BitVector': dict(**{'from': al, 'to': ar}, hypotheses=[], certificate=cert)})})
        return trans(convert(left, nl), {'Use': dict(theorem=theorem, arguments=opaque, premises=[])}, convert(nr, right))

    identity_proof = word_fact(c(zero, a), a, ['a'])
    associativity = word_fact(c(c(a, b), var('c')), c(a, c(b, var('c'))), ['a', 'b', 'c'])
    commutativity = word_fact(c(a, b), c(b, a), ['a', 'b'])
    commute_theorem = add({'Theorem': dict(params=[['a', 'U64'], ['b', 'U64']], conditions=[],
                                           **{'from': c(a, b), 'to': c(b, a)}, proof=commutativity)})
    extremum = convert(c(a, b), body)

    # Factorisation: the keep's query over the rows equals the fixed fold.
    node = cons(rows, 1, [key, row, tail])
    left_cons = normal(q(node), objects)
    inner = normal(q(tail), objects)
    if replace(left_cons, inner, var('extremum_hole')) == left_cons:
        raise ValueError('keep does not unfold to its tail value')
    context = replace(left_cons, inner, var('extremum_hole'))
    after_ih = replace(left_cons, inner, total(tail))
    step = trans(convert(q(node), left_cons),
                 {'Substitute': dict(variable='extremum_hole', context=context, equality={'Hypothesis': 0})},
                 word_fact(after_ih, total(node), []))
    xs = var('rows')
    lemma = add({'Theorem': dict(params=[['rows', {'Data': rows}]], conditions=[], **{'from': q(xs), 'to': total(xs)},
                                 proof={'Induction': dict(variable='rows', **{'from': q(xs), 'to': total(xs)}, cases=[
                                     dict(bindings=[], proof=convert(q(nil), total(nil))),
                                     dict(bindings=['key', 'row', 'tail'], proof=step)])})},
                [i for i, o in objects.items() if 'Datatype' in o['payload'].get('declaration', {})])
    actual = var(binding)
    factorisation = trans(convert(query, q(actual)), {'Use': dict(theorem=lemma, arguments=[actual], premises=[])})

    # Insertion: combine(total(tail), c(row)) = total(node(row)), by commutativity.
    insertion = trans({'Use': dict(theorem=commute_theorem, arguments=[total(tail), contrib(row)], premises=[])},
                      convert(c(contrib(row), total(tail)), total(node)))
    return dict(keep=subject['keep'], table=subject['table'], contribution=contribution, combine=combine, zero=zero,
                factorisation=factorisation, identity=identity_proof, associativity=associativity,
                commutativity=commutativity, insertion=insertion, extremum=dict(order=order, proof=extremum))
