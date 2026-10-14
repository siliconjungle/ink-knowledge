"""Bounded literal-loop expansion as ordinary database normalization proofs.

A small proposal budget limits expansion. It grants no rewrite authority or
profitability claim; source binding and fixed loop semantics stay in the checker.
"""
from producers.semantic_laws import value, var, word, term, op, arrow, law


def specialize(subject, core):
    from ink_planner.semantic_search import positions
    from ink_knowledge import canonical
    rows, seen = [], set()
    for body in subject.get('functions', {}).values():
        for _, source in positions(body):
            node = source['node']
            call = node.get('Op') if isinstance(node, dict) else None
            if not call or call[0] != 'call:repeat' or len(call[1]) != 3:
                continue
            count = call[1][0]['node'].get('Nat')
            if type(count) is not int or not 0 <= count <= 8:
                continue
            sort = source['sort']
            step_sort = arrow(value('U32'), arrow(sort, sort))
            if call[1][1]['sort'] != sort or call[1][2]['sort'] != step_sort:
                continue
            key = canonical([sort, count])
            if key in seen:
                continue
            seen.add(key)
            initial, step = var(sort, 'initial'), var(step_sort, 'step')
            left = op(sort, 'call:repeat', term('Nat', {'Nat': count}), initial, step)
            right = initial
            for i in range(count):
                right = op(sort, 'apply', op(arrow(sort, sort), 'apply', step, word('U32', i)), right)
            rows.append(('literal-loop/'+str(count)+'/'+str(len(rows)),
                         law({'initial':sort, 'step':step_sort}, left, right)))
            if len(rows) >= 128:
                return rows
    return rows
