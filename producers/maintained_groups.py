"""Untrusted authoring of grouped maintained views for one-parameter queries.

A source query `q(p)` over one table whose per-row unfolding adds a word
contribution exactly for rows whose group word equals `p` becomes an
`ink-maintained-fold-v1` view with a `group` function. The core checks the
exact factorisation `q(p) = fold(rows, p)` for every parameter, the wrapping
word group laws, and the per-cell equations of the grouped fold; the fixed
controller keeps one total per group. Every word fact is a bit-vector
certificate the kernel replays. Shapes that do not unfold this way decline.
"""
from producers.action_replacement import var, call, cons, convert, trans
from producers.point_delta import binary, normal, sub, replace, free_variables

WORD_OPS = {'+', '-', '*', '&'}
COMPARE = {'<', '>', '<=', '>=', '==', '!='}
BOOL_OPS = {'&&', '||'}
HOLE = 'grouped_hole'


def _if(condition, on_true, on_false):
    return {'If': dict(condition=condition, on_true=on_true, on_false=on_false)}


def _bool(t):
    """Whether a term is evidently Boolean from its own shape."""
    if 'Bool' in t:
        return True
    if 'Binary' in t:
        return t['Binary']['op'] in COMPARE | BOOL_OPS
    return False


def abstract(terms, sorts=None):
    """Replace maximal subterms outside the word/Boolean fragment by shared
    variables, with their sorts, so a bit-vector certificate can state the
    remaining fact."""
    opaque = []

    def leaf(t, sort):
        for i, (o, s) in enumerate(opaque):
            if o == t:
                if s != sort:
                    raise ValueError('grouped abstraction sort conflict')
                return var('grouped_word_' + str(i))
        opaque.append((t, sort))
        return var('grouped_word_' + str(len(opaque) - 1))

    def walk(t, sort):
        if isinstance(t, dict):
            if 'U64' in t or 'Bool' in t:
                return t
            if 'Binary' in t:
                x = t['Binary']
                op = x['op']
                if op in WORD_OPS and sort == 'U64':
                    return binary(op, walk(x['left'], 'U64'), walk(x['right'], 'U64'))
                if op in BOOL_OPS and sort == 'Bool':
                    return binary(op, walk(x['left'], 'Bool'), walk(x['right'], 'Bool'))
                if op in COMPARE and sort == 'Bool':
                    inner = 'Bool' if op in ('==', '!=') and (_bool(x['left']) or _bool(x['right'])) else 'U64'
                    return binary(op, walk(x['left'], inner), walk(x['right'], inner))
            if 'If' in t:
                x = t['If']
                return _if(walk(x['condition'], 'Bool'), walk(x['on_true'], sort), walk(x['on_false'], sort))
        return leaf(t, sort)
    sorts = sorts or ['U64'] * len(terms)
    return [walk(t, s) for t, s in zip(terms, sorts)], opaque


def conditions(t):
    """If conditions in `t` that contain no further conditional."""
    if isinstance(t, dict):
        if 'If' in t:
            c = t['If']['condition']
            if not any(conditions(c)):
                yield c
        for x in t.values():
            yield from conditions(x)
    elif isinstance(t, list):
        for x in t:
            yield from conditions(x)


def _group_condition(t, parameter):
    """The `G == p` comparisons in `t` whose other side is free of `p`."""
    found = []

    def walk(t):
        if isinstance(t, dict):
            if 'Binary' in t and t['Binary']['op'] == '==':
                a, b = t['Binary']['left'], t['Binary']['right']
                for this, other in ((a, b), (b, a)):
                    if this == var(parameter) and parameter not in free_variables(other):
                        found.append((t, other))
            for x in t.values():
                walk(x)
        elif isinstance(t, list):
            for x in t:
                walk(x)
    walk(t)
    return found


def author(subject, objects, add, compiler, certificates, combine, inverse, laws, ring):
    """One grouped view for a one-parameter query, or raise ValueError."""
    from producers.sorted_rows import word_certificate
    from producers.point_delta import lift
    from ink_knowledge.store import entry
    from ink_knowledge import identity
    from producers.representations import match
    if subject['result'] != 'U64':
        raise ValueError('grouped views author wrapping word sums')
    parameter = subject.get('parameter')
    if not parameter:
        raise ValueError('grouped views need a query parameter')
    rows = subject['rows']
    binding = subject['bindings'][subject['root']]
    query = subject['value']
    q = lambda r: sub(query, {binding: r})
    key, row, tail, p = var('key'), var('row'), var('tail'), var(parameter)
    nil = cons(rows, 0, [])
    node = cons(rows, 1, [key, row, tail])
    zero = {'U64': 0}
    if normal(q(nil), objects) != zero:
        raise ValueError('query over an empty table is not the word sum identity')
    # A single row's value: its contribution when its group is the parameter.
    single = normal(q(cons(rows, 1, [key, row, nil])), objects)
    comparisons = _group_condition(single, parameter)
    if len({canonical_json(g) for _, g in comparisons}) != 1:
        raise ValueError('query does not select rows by one group word equal to its parameter')
    group_term = comparisons[0][1]
    if free_variables(group_term) - {'key', 'row'}:
        raise ValueError('group word depends on more than the row')
    selected = single
    for comparison, _ in comparisons:
        selected = replace(selected, comparison, {'Bool': True})
    def expand(t, depth=0):
        """Shannon-expand stuck conditionals so every branch is a plain word."""
        t = normal(t, objects)
        c = next(conditions(t), None)
        if c is None:
            return t
        if depth > 6:
            raise ValueError('grouped contribution case budget')
        yes, no = expand(replace(t, c, {'Bool': True}), depth + 1), expand(replace(t, c, {'Bool': False}), depth + 1)
        return yes if yes == no else _if(c, yes, no)
    contribution_body = expand(selected)
    if free_variables(contribution_body) - {'key', 'row'}:
        raise ValueError('row contribution depends on the parameter')
    group = add({'Function': dict(params=[['key', subject['key']], ['row', subject['row']]], result='U64',
                                  body=group_term, recursive=None)})
    contribution = add({'Function': dict(params=[['key', subject['key']], ['row', subject['row']]], result='U64',
                                         body=contribution_body, recursive=None)})
    c = lambda x, y: call(combine, [x, y])

    def masked(r, parameter_term):
        return _if(binary('==', call(group, [key, r]), parameter_term), call(contribution, [key, r]), zero)

    # The core's fixed grouped fold meaning (core/src/maintained.rs `fold`).
    gp = var('group_parameter')
    declaration = {'Function': dict(params=[['rows', {'Data': rows}], ['group_parameter', 'U64']], result='U64', recursive=0,
                                    body=match(var('rows'), [([], zero), (['key', 'row', 'tail'],
                                                                          c(masked(row, gp), {'SelfCall': [tail, gp]}))]))}
    exact = entry('definition', 'first-order-inductive-equality-v1', dict(declaration=declaration),
                  sorted({rows, contribution, combine, group}),
                  parameters={'rows': {'Data': rows}, 'group_parameter': 'U64'}, result='U64')
    fold = identity(exact)
    objects[fold] = exact
    total = lambda r, at: call(fold, [r, at])

    def word_fact(lhs, rhs, facts=()):
        """`lhs = rhs` for word terms under Boolean case facts
        (condition, value, hypothesis index): normalise, then a certificate
        for the abstracted identity, instantiated by Use."""
        nl, nr = normal(lhs, objects), normal(rhs, objects)
        if nl == nr:
            return convert(lhs, rhs)
        terms, opaque = abstract([nl, nr, *[f[0] for f in facts]], ['U64', 'U64', *['Bool'] * len(facts)])
        names = [['grouped_word_' + str(i), s] for i, (_, s) in enumerate(opaque)]
        conds = [dict(**{'from': t, 'to': {'Bool': f[1]}}) for t, f in zip(terms[2:], facts)]
        goal = dict(params=names, conditions=conds, **{'from': terms[0], 'to': terms[1]})
        cert = word_certificate(compiler, goal, certificates)
        theorem = add({'Theorem': dict(**goal, proof={'BitVector': dict(**{'from': terms[0], 'to': terms[1]},
                                                                         hypotheses=list(range(len(facts))), certificate=cert)})})
        return trans(convert(lhs, nl), {'Use': dict(theorem=theorem, arguments=[o for o, _ in opaque],
                                                     premises=[{'Hypothesis': f[2]} for f in facts])}, convert(nr, rhs))

    def simplify(t, rewrites):
        """Normalise and rewrite with hypotheses until stable."""
        current = normal(t, objects)
        proof = convert(t, current)
        for _ in range(32):
            changed = False
            for left, right, index in rewrites:
                updated = replace(current, left, right)
                if updated != current:
                    proof = trans(proof, lift({'Hypothesis': index}, replace(current, left, var('delta_hole'))),
                                  convert(updated, normal(updated, objects)))
                    current = normal(updated, objects)
                    changed = True
            if not changed:
                return current, proof
        raise ValueError('grouped rewrite budget')

    arithmetic_cache = {}

    def arithmetic(a, z):
        """`a = z` for If-free word sums by the replayed ring derivation."""
        opaque = []

        def walk(t):
            if 'U64' in t:
                return t
            if 'Binary' in t and t['Binary']['op'] in ('+', '-', '*'):
                x = t['Binary']
                return binary(x['op'], walk(x['left']), walk(x['right']))
            if t not in opaque:
                opaque.append(t)
            return var('grouped_ring_' + str(opaque.index(t)))
        aa, zz = walk(a), walk(z)
        key = canonical_json([aa, zz])
        if key not in arithmetic_cache:
            params = [['grouped_ring_' + str(i), 'U64'] for i in range(len(opaque))]
            arithmetic_cache[key] = add({'Theorem': dict(params=params, conditions=[], **{'from': aa, 'to': zz},
                                                         proof=ring.prove(aa, zz))})
        return {'Use': dict(theorem=arithmetic_cache[key], arguments=opaque, premises=[])}

    contradictions = {}

    def contradiction(a, z, facts):
        """`a = z` when the case facts cannot hold together, else None."""
        terms, opaque = abstract([f[0] for f in facts], ['Bool'] * len(facts))
        key = canonical_json([terms, [f[1] for f in facts]])
        if key not in contradictions:
            names = [['grouped_word_' + str(i), s] for i, (_, s) in enumerate(opaque)]
            sides = [var('grouped_left'), var('grouped_right')]
            goal = dict(params=names + [['grouped_left', 'U64'], ['grouped_right', 'U64']],
                        conditions=[dict(**{'from': t, 'to': {'Bool': f[1]}}) for t, f in zip(terms, facts)],
                        **{'from': sides[0], 'to': sides[1]})
            try:
                cert = word_certificate(compiler, goal, certificates)
            except Exception:
                contradictions[key] = None
            else:
                contradictions[key] = add({'Theorem': dict(**goal, proof={'BitVector': dict(
                    **{'from': sides[0], 'to': sides[1]}, hypotheses=list(range(len(facts))), certificate=cert)})})
        theorem = contradictions[key]
        if theorem is None:
            return None
        return {'Use': dict(theorem=theorem, arguments=[o for o, _ in opaque] + [a, z],
                            premises=[{'Hypothesis': f[2]} for f in facts])}

    def prove(a, z, ih, facts, depth=0):
        """Split on conditions until no conditional remains, closing each case
        by the induction hypothesis and ring arithmetic, or by contradictory
        case facts."""
        if depth > 8:
            raise ValueError('grouped case budget')
        rewrites = ([(normal(ih[0], objects), ih[1], ih[2])] if ih else []) + [(f[0], {'Bool': f[1]}, f[2]) for f in facts]
        na, pa = simplify(a, rewrites)
        nz, pz = simplify(z, rewrites)
        if na == nz:
            return trans(pa, {'Sym': pz})
        if len(facts) > 1:
            closed = contradiction(na, nz, facts)
            if closed is not None:
                return trans(pa, closed, {'Sym': pz})
        known = [f[0] for f in facts]
        blocked = next((x for x in [*conditions(na), *conditions(nz)] if x not in known), None)
        if blocked is not None:
            index = (1 if ih else 0) + len(facts)
            branches = {('on_true' if flag else 'on_false'): prove(a, z, ih, [*facts, (blocked, flag, index)], depth + 1)
                        for flag in (False, True)}
            return {'BoolSplit': dict(condition=blocked, **{'from': a, 'to': z}, **branches)}
        return trans(pa, arithmetic(na, nz), {'Sym': pz})

    # Factorisation: the query equals the grouped fold for every parameter.
    xs = var('rows')
    step = prove(q(node), total(node, p), (q(tail), total(tail, p), 0), [])
    lemma = add({'Theorem': dict(params=[['rows', {'Data': rows}], [parameter, 'U64']], conditions=[],
                                 **{'from': q(xs), 'to': total(xs, p)},
                                 proof={'Induction': dict(variable='rows', **{'from': q(xs), 'to': total(xs, p)}, cases=[
                                     dict(bindings=[], proof=convert(q(nil), total(nil, p))),
                                     dict(bindings=['key', 'row', 'tail'], proof=step)])})},
                [i for i, o in objects.items() if 'Datatype' in o['payload'].get('declaration', {})])
    actual = var(binding)
    factorisation = trans(convert(query, q(actual)), {'Use': dict(theorem=lemma, arguments=[actual, p], premises=[])})

    # Per-cell equations of the grouped fold.
    at = lambda r: cons(rows, 1, [key, r, tail])
    m = lambda r: masked(r, gp)
    neg = call(inverse, [m(row)])
    mutations = dict(
        insertion=prove(c(total(tail, gp), m(row)), total(at(row), gp), None, []),
        deletion=prove(c(total(at(row), gp), neg), total(tail, gp), None, []),
        replacement=prove(c(total(at(row), gp), c(neg, m(var('new')))), total(at(var('new')), gp), None, []),
    )
    return dict(keep=subject['keep'], table=subject['table'], contribution=contribution, combine=combine,
                inverse=inverse, zero=zero, factorisation=factorisation, group=group, **laws, **mutations)


def canonical_json(t):
    import json
    return json.dumps(t, sort_keys=True, separators=(',', ':'))
