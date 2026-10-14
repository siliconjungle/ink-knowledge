"""Ordinary word induction for independent, equally bounded record reductions.

Only loops whose stop callbacks reduce to false are proposed here. Every lane
retains the same wrapping index and step order. Discovery, proof and subsequent
profitability selection remain separate.
"""
from ink_knowledge import identity, semantic_entry
from ink_planner.semantic_search import positions, children, shift, substitute
from producers.semantic_laws import value, var, bound, lam, op, law, term, word
from producers.owned_fold_contracts import closed
from producers.beta_specialization15 import beta_normalize
from producers.definition_context28 import bind


def specialize(subject, core=None):
    if not core:
        return []
    u, boolean = value('U32'), value('Bool')
    false = term(boolean, {'Bool': False})
    one, zero = word('U32', 1), word('U32', 0)
    def operation(t):
        return t['node'].get('Op') if isinstance(t['node'], dict) else None
    def free(t, params):
        node = t['node']
        if isinstance(node, dict) and 'Free' in node:
            params[node['Free']] = t['sort']
        for child in children(t):
            free(child, params)
    def apply(f, x):
        return op(f['sort']['Arrow'][1], 'apply', f, x)
    def advance(f, i, s):
        return apply(apply(f, i), s)
    def trans(m, a, b):
        return {'Trans': dict(middle=m, left=a, right=b)}
    def choose(c, a, b):
        return op(a['sort'], 'call:choose', c, a, b)
    rows = []
    for function, root in sorted(subject['functions'].items()):
        for path, source in positions(root):
            record = operation(source)
            if not record or not record[0].startswith('record:') or not closed(source):
                continue
            fields = core['program']['records'].get(record[0][7:], [])
            loops = [operation(t) for t in record[1]]
            if not 2 <= len(fields) <= 8 or len(fields) != len(loops):
                continue
            if any(not f or f[0] != 'call:repeat_until' or len(f[1]) != 4 for f in loops):
                continue
            if any(f[1][0] != loops[0][1][0] for f in loops):
                continue
            if any(beta_normalize(apply(f[1][2], f[1][1])) != false or
                   beta_normalize(f[1][2]) != lam(f[1][1]['sort'], false) for f in loops):
                continue
            callbacks = [f[1][3] for f in loops]
            params = {}
            for f in callbacks:
                free(f, params)
            used = set(params)
            def fresh(n):
                while n in used:
                    n += '_'
                used.add(n)
                return n
            count_name, index_name = fresh('product_count'), fresh('product_index')
            previous_name = fresh('product_previous')
            state_names = [fresh('product_state_' + str(i)) for i in range(len(fields))]
            count, index, previous = (var(u, n) for n in [count_name, index_name, previous_name])
            seeds = [var(t['sort'], n) for t, n in zip(record[1], state_names)]
            pack = lambda states: op(source['sort'], record[0], *states)
            stop = lambda state: lam(state['sort'], false)
            callback = beta_normalize(lam(u, lam(source['sort'], pack([
                advance(shift(f, 2), bound(u, 1), op(s['sort'], 'field:' + name, bound(source['sort'], 0)))
                for (name, _), s, f in zip(fields, seeds, callbacks)]))))
            def run(n, i, s, f):
                return op(s['sort'], 'until.from', n, i, s, stop(s), f)
            def separate(n, i, states):
                return pack([run(n, i, s, f) for s, f in zip(states, callbacks)])
            def fused(n, i, states):
                return run(n, i, pack(states), callback)
            successor = op(u, 'binary:+', previous, one)
            next_index = op(u, 'binary:+', index, one)
            remaining = op(u, 'binary:-', successor, one)
            is_zero = op(boolean, 'binary:==', successor, zero)
            advanced = [advance(f, index, s) for s, f in zip(seeds, callbacks)]
            def unfolded(s, f):
                return choose(is_zero, s, choose(apply(stop(s), s), s,
                    run(remaining, next_index, advance(f, index, s), f)))
            raw_left = pack([unfolded(s, f) for s, f in zip(seeds, callbacks)])
            simple_left = pack([choose(is_zero, s, run(previous, next_index, a, f))
                                for s, a, f in zip(seeds, advanced, callbacks)])
            raw_right = unfolded(pack(seeds), callback)
            simple_right = choose(is_zero, pack(seeds), fused(previous, next_index, advanced))
            ih_args = {index_name: next_index, **dict(zip(state_names, advanced))}
            recurse = trans(separate(previous, next_index, advanced), 'Normalize',
                trans(fused(previous, next_index, advanced),
                    {'GeneralizedHypothesis': dict(index=0, arguments=ih_args)}, 'Normalize'))
            branches = {'Cases': dict(condition=is_zero, on_true='Normalize', on_false=recurse)}
            proof = trans(raw_left, {'Congruence': ['Unfold'] * len(fields)},
                trans(simple_left, 'Normalize', trans(simple_right, branches,
                    {'Sym': trans(raw_right, 'Unfold', 'Normalize')})))
            params.update({count_name: u, index_name: u, **{n: s['sort'] for n, s in zip(state_names, seeds)}})
            general = law(params, separate(count, index, seeds), fused(count, index, seeds),
                {'GeneralizedInduction': dict(variable=count_name, generalize=[index_name, *state_names],
                    names=[previous_name], base='Normalize', step=proof)})
            general['semantics'] = 'ink-general-laws-v1'
            general = bind(general, core, subject)
            key = identity(semantic_entry(general))
            public = lambda s, f: op(s['sort'], 'call:repeat_until', count, s, stop(s), f)
            left, right = pack([public(s, f) for s, f in zip(seeds, callbacks)]), public(pack(seeds), callback)
            arguments = {n: var(s, n) for n, s in params.items()}
            arguments[index_name] = zero
            use = {'Use': dict(law=key, arguments=arguments, premises=[])}
            proof = trans(substitute(general['from'], arguments), {'Congruence': ['Unfold'] * len(fields)},
                          trans(substitute(general['to'], arguments), use, {'Sym': 'Unfold'}))
            public_params = {n: s for n, s in params.items() if n != index_name}
            concrete = law(public_params, left, right, proof, dependencies=[key])
            concrete['semantics'] = 'ink-general-laws-v1'
            concrete = bind(concrete, core, subject)
            label = function + '_ordered_loop_product_' + '_'.join(map(str, path))
            rows.extend([(label + '_induction', general), (label, concrete)])
            if len(rows) >= 64:
                return rows
    return rows
