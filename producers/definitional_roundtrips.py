"""Bounded proof proposals for ordinary source codec inverses.

Calculation is untrusted. Every beta/projection/unfold and normalization step
must replay in the existing equality checker with the exact source context.
No function name, record name or codec annotation grants rewrite authority.
"""
from producers.semantic_laws import law, op, value, var
from producers.definition_context28 import bind


def _map(term, visit, depth=0):
    result = dict(term)
    node = term['node']
    if isinstance(node, dict):
        if 'Lambda' in node:
            result['node'] = {'Lambda': visit(node['Lambda'], depth + 1)}
        elif 'Op' in node:
            result['node'] = {'Op': [node['Op'][0], [visit(x, depth) for x in node['Op'][1]]]}
        elif 'Cons' in node:
            result['node'] = {'Cons': [visit(x, depth) for x in node['Cons']]}
    return result


def _shift(term, amount, cutoff=0):
    node = term['node']
    if isinstance(node, dict) and 'Bound' in node and node['Bound'] >= cutoff:
        return dict(term, node={'Bound': node['Bound'] + amount})
    return _map(term, lambda child, depth: _shift(child, amount, depth), cutoff)


def _beta(body, argument, depth=0):
    node = body['node']
    if isinstance(node, dict) and 'Bound' in node:
        index = node['Bound']
        if index == depth:
            return _shift(argument, depth)
        if index > depth:
            return dict(body, node={'Bound': index - 1})
    return _map(body, lambda child, level: _beta(child, argument, level), depth)


def _substitute(body, arguments, depth=0):
    node = body['node']
    if isinstance(node, dict) and node.get('Free') in arguments:
        return _shift(arguments[node['Free']], depth)
    return _map(body, lambda child, level: _substitute(child, arguments, level), depth)


def propose(core, subject, function, *, steps=4096):
    functions = {f['name']: f for f in core['program']['functions']}
    records = core['program']['records']
    declaration = functions[function]
    if len(declaration['params']) != 1 or declaration['params'][0][1] != declaration['result']:
        raise ValueError('inverse observer must have one argument and the same result type')
    remaining = [steps]

    def chain(before, after, proof, tail):
        if before == after:
            return tail
        return {'Trans': dict(middle=after, left=proof, right=tail)}

    def reduce(term, depth=0):
        remaining[0] -= 1
        if remaining[0] < 0 or depth >= 96:
            raise ValueError('definition proof proposal budget')
        node = term['node']
        call = node.get('Op') if isinstance(node, dict) else None
        if not call:
            return term, 'Normalize'
        name, arguments = call
        after = None
        if name.startswith('call:') and name[5:] in functions:
            f = functions[name[5:]]
            after = _substitute(subject['functions'][name[5:]], dict(zip((n for n, _ in f['params']), arguments)))
        elif name == 'apply' and isinstance(arguments[0]['node'], dict) and 'Lambda' in arguments[0]['node']:
            after = _beta(arguments[0]['node']['Lambda'], arguments[1])
        if after is not None:
            result, proof = reduce(after, depth + 1)
            return result, chain(term, after, 'Unfold', proof)

        # A projection first reduces only its receiver, then selects one field.
        # This avoids expanding unrelated fields before a projection discards them.
        if name.startswith('field:'):
            receiver, proof = reduce(arguments[0], depth + 1)
            middle = op(term['sort'], name, receiver)
            constructor = receiver['node'].get('Op') if isinstance(receiver['node'], dict) else None
            if constructor and constructor[0].startswith('record:'):
                fields = records[constructor[0][7:]]
                index = next(i for i, (field, _) in enumerate(fields) if field == name[6:])
                after = constructor[1][index]
                result, tail = reduce(after, depth + 1)
                tail = chain(middle, after, 'Unfold', tail)
                return result, chain(term, middle, {'Congruence': [proof]}, tail)
            return middle, {'Congruence': [proof]}

        children = [reduce(x, depth + 1) for x in arguments]
        middle = op(term['sort'], name, *(x for x, _ in children))
        after = middle
        args = middle['node']['Op'][1]
        if name == 'method:freeze' and len(args) == 1:
            buffer = args[0]['node'].get('Op') if isinstance(args[0]['node'], dict) else None
            if buffer and buffer[0] == 'call:buffer':
                after = buffer[1][0]
        if name.startswith('record:') and args:
            projections = [x['node'].get('Op') if isinstance(x['node'], dict) else None for x in args]
            fields = records[name[7:]]
            if len(fields) == len(args) and all(p and p[0] == 'field:' + f for p, (f, _) in zip(projections, fields)):
                receiver = projections[0][1][0]
                if all(p[1] == [receiver] for p in projections):
                    after = receiver
        proof = chain(term, middle, {'Congruence': [p for _, p in children]}, 'Normalize')
        return after, proof

    parameter, ty = declaration['params'][0]
    argument = var(value(ty), parameter)
    source = op(value(ty), 'call:' + function, argument)
    result, proof = reduce(source)
    if result != argument:
        raise ValueError('definition calculation did not establish the inverse')
    candidate = law({parameter: value(ty)}, source, argument, proof)
    candidate['semantics'] = 'ink-general-laws-v1'
    return bind(candidate, core, subject, [function])
