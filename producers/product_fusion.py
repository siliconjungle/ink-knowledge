"""Propose ordered product folds over arbitrary independent record fields.

The record and callbacks come from checked source. Structural induction replays
the whole replacement; recognition grants no authority and makes no cost claim.
Each lane retains its original input and arithmetic order, including F32.
"""
from producers.semantic_laws import value, var, bound, lam, op, law
from producers.owned_fold_contracts import closed
from producers.beta_specialization15 import beta_normalize
from producers.definition_context28 import bind


def specialize(subject, core=None):
    if not core:
        return []
    from ink_planner.semantic_search import positions, children, shift

    def operation(t):
        node = t['node']
        return node.get('Op') if isinstance(node, dict) else None

    def free(t, params):
        node = t['node']
        if isinstance(node, dict) and 'Free' in node:
            params[node['Free']] = t['sort']
        for child in children(t):
            free(child, params)

    def apply(f, x):
        return op(f['sort']['Arrow'][1], 'apply', f, x)

    rows = []
    for function, root in sorted(subject['functions'].items()):
        for path, source in positions(root):
            record = operation(source)
            if not record or not record[0].startswith('record:') or not closed(source):
                continue
            fields = core['program']['records'].get(record[0][7:], [])
            if not 2 <= len(fields) <= 8 or len(fields) != len(record[1]):
                continue
            folds = [operation(t) for t in record[1]]
            if any(not f or f[0] != 'call:foldl' or len(f[1]) != 3 for f in folds):
                continue
            sequence = folds[0][1][0]
            if any(f[1][0] != sequence for f in folds):
                continue
            params = {}
            for f in folds:
                free(f[1][2], params)
            names = set(params)

            def fresh(prefix):
                while prefix in names:
                    prefix += '_'
                names.add(prefix)
                return prefix

            xs_name = fresh('product_items')
            state_names = [fresh('product_state_' + str(i)) for i in range(len(fields))]
            xs = var(sequence['sort'], xs_name)
            states = [var(t['sort'], n) for t, n in zip(record[1], state_names)]
            callbacks = [f[1][2] for f in folds]
            item_sort = value(sequence['sort']['Value']['List'])
            item, accumulator = bound(item_sort, 1), bound(source['sort'], 0)
            updates = [apply(apply(shift(f, 2), item), op(t['sort'], 'field:' + name, accumulator))
                       for (name, _), t, f in zip(fields, states, callbacks)]
            callback = lam(item_sort, lam(source['sort'], op(source['sort'], record[0], *updates)))
            callback = beta_normalize(callback)

            def separate(sequence, seeds):
                return op(source['sort'], record[0], *[
                    op(seed['sort'], 'call:foldl', sequence, seed, step)
                    for seed, step in zip(seeds, callbacks)])

            def fused(sequence, seeds):
                return op(source['sort'], 'call:foldl', sequence,
                          op(source['sort'], record[0], *seeds), callback)

            head_name, tail_name = fresh('product_head'), fresh('product_tail')
            head, tail = var(item_sort, head_name), var(xs['sort'], tail_name)
            advanced = [apply(apply(step, head), seed) for step, seed in zip(callbacks, states)]
            ih = {'GeneralizedHypothesis': dict(index=0, arguments=dict(zip(state_names, advanced)))}
            step = {'Trans': dict(middle=separate(tail, advanced), left='Normalize', right={
                'Trans': dict(middle=fused(tail, advanced), left=ih, right='Normalize')})}
            proof = {'GeneralizedInduction': dict(variable=xs_name, generalize=state_names,
                      names=[head_name, tail_name], base='Normalize', step=step)}
            params.update({xs_name: xs['sort'], **{n: s['sort'] for n, s in zip(state_names, states)}})
            proposed = bind(law(params, separate(xs, states), fused(xs, states), proof), core, subject)
            rows.append((function + '_ordered_product_' + '_'.join(map(str, path)), proposed))
            if len(rows) >= 64:
                return rows
    return rows
