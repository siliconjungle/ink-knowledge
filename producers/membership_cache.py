"""Proved cache retention for observations which read keys rather than payloads.

Ordinary row induction checks every proposed helper law. Unknown functions or
membership changes refresh the exact cache. No producer metadata is trusted.
"""
from action_replacement import var, call, cons, convert, trans
from point_delta import normal, equality, binary, sub, replace, lift
from cache_maintenance import leaves, variables


def setup(model, cache, add, objects):
    observers = {}
    for fid, entry in list(objects.items()):
        f = entry['payload'].get('declaration', {}).get('Function')
        if not f or f['recursive'] != 0 or not f['params']:
            continue
        table = next((t for t in model['tables'] if f['params'][0][1] == {'Data': t['datatype']}), None)
        body = f['body'].get('Match', {})
        if not table or body.get('scrutinee') != var(f['params'][0][0]):
            continue
        branches = body.get('branches', [])
        if len(branches) != 2 or len(branches[1]['bindings']) != 3:
            continue
        h, payload, tail = branches[1]['bindings']
        if payload in variables(branches[1]['body']):
            continue
        # Changing a value leaves this helper's output unchanged. Generalise
        # the other arguments so the law also covers parameterised selection.
        rows = var('membership_rows'); key = var('membership_key'); value = var('membership_value')
        params = [['membership_rows', {'Data': table['datatype']}], ['membership_key', f['params'][0][1]]]
        params[1][1] = objects[table['replace']]['payload']['declaration']['Function']['params'][1][1]
        params.append(['membership_value', objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]])
        params.extend(f['params'][1:]); rest = [var(n) for n, _ in f['params'][1:]]
        lhs = lambda r: call(fid, [call(table['replace'], [r, key, value]), *rest])
        rhs = lambda r: call(fid, [r, *rest])
        nil = cons(table['datatype'], 0, [])
        bound = cons(table['datatype'], 1, [var(h), var(payload), var(tail)])
        guard = binary('==', key, var(h))
        branches_proof = {}
        for flag in [False, True]:
            branches_proof['on_true' if flag else 'on_false'] = equality(lhs(bound), rhs(bound), objects,
                (lhs(var(tail)), rhs(var(tail)), 0), [(guard, {'Bool': flag}, 1)])
        proof = {'Induction': dict(variable='membership_rows', **{'from': lhs(rows), 'to': rhs(rows)}, cases=[
            dict(bindings=[], proof=convert(lhs(nil), rhs(nil))),
            dict(bindings=[h, payload, tail], proof={'BoolSplit': dict(condition=guard, **{'from': lhs(bound), 'to': rhs(bound)}, **branches_proof)})])}
        law = add({'Theorem': dict(params=params, conditions=[], **{'from': lhs(rows), 'to': rhs(rows)}, proof=proof)})
        observers[fid] = (table, law)
    reply = cache['case']['normal']['Construct']['arguments'][0]

    def rewrite(term):
        if 'Call' not in term:
            return term, {'Refl': term}
        x = term['Call']; args = []; proofs = []
        for arg in x['arguments']:
            z, p = rewrite(arg); args.append(z); proofs.append(p)
        current = call(x['function'], args)
        proof = {'Call': dict(function=x['function'], arguments=proofs)}
        if x['function'] in observers:
            table, law = observers[x['function']]
            while 'Call' in args[0] and args[0]['Call']['function'] == table['replace']:
                changed = args[0]['Call']['arguments']
                step = {'Use': dict(theorem=law, arguments=[*changed, *args[1:]], premises=[])}
                proof = trans(proof, step); args[0] = changed[0]; current = call(x['function'], args)
        return current, proof

    def at_roots(roots, bindings):
        target = sub(reply, dict(zip(cache['case']['bindings'], roots)))
        simplified, proof = rewrite(target)
        original = sub(reply, dict(zip(cache['case']['bindings'], map(var, bindings))))
        if normal(simplified, objects) != normal(original, objects):
            raise ValueError('membership changed or unsupported observer')
        return trans(proof, convert(simplified, original))

    def action(sa):
        try:
            for o in leaves(sa['case']['normal']):
                if o['constructor'] == 0 and o['arguments'][1] == {'Bool': True}:
                    at_roots(o['arguments'][3]['Construct']['arguments'], sa['case']['bindings'])
            return var('cached_reply')
        except (ValueError, KeyError):
            return None
    return dict(action=action, roots=True, equality=at_roots, recipe=lambda roots, old, bindings: old)
