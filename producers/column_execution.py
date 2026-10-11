"""Compile an action's ordinary source projection to proved column operations.

The output includes the complete logical observation for admission. Standalone
lowering erases its private state; snapshots continue to use the exact decoder.
"""
from producers.action_replacement import var, call, cons, convert, trans
from producers.point_delta import sub, replace
from producers.representations import match


def transform(model, action, layout, physical_id, order, extra, objects):
    roots = action['case']['bindings']
    names = ['root_' + str(i) for i in range(len(roots))]
    source_roots = [var(n) for n in names]
    encoded_roots = [call(layout['encode'][i], [r]) for i, r in enumerate(source_roots)]
    facts = dict(zip(names, encoded_roots))

    def use(key, args):
        return {'Use': dict(theorem=key, arguments=args, premises=[])}

    def lift(proof, context):
        return {'Substitute': dict(variable='column_hole', context=context, equality=proof)}

    def arguments(original, transformed, proofs, rebuild):
        current = list(transformed)
        steps = []
        for i, proof in enumerate(proofs):
            if current[i] == original[i]:
                continue
            hole = current.copy(); hole[i] = var('column_hole')
            steps.append(lift(proof, rebuild(hole)))
            current[i] = original[i]
        return steps

    def root(t, index):
        table = model['tables'][index]
        if t == var(roots[index]):
            return var(names[index]), {'Refl': encoded_roots[index]}, source_roots[index]
        if 'Call' in t:
            c = t['Call']
            operation = next((n for n in ['insert', 'remove', 'replace'] if table[n] == c['function']), None)
            if operation:
                r, rp, original_root = root(c['arguments'][0], index)
                values = [value(a) for a in c['arguments'][1:]]
                physical_args = [r, *[a for a, _, _ in values]]
                original_args = [call(layout['encode'][index], [original_root]), *[z for _, _, z in values]]
                proofs = [rp, *[p for _, p, _ in values]]
                physical = call(layout['operations'][index][operation], physical_args)
                start = sub(physical, facts)
                steps = arguments(original_args, [sub(a, facts) for a in physical_args], proofs,
                                  lambda xs: call(layout['operations'][index][operation], xs))
                changed = call(table[operation], [original_root, *original_args[1:]])
                law = use(layout['operation_laws'][index][operation], [original_root, *original_args[1:]])
                end = call(layout['encode'][index], [changed])
                return physical, trans(*steps, law, convert(law_term(index, operation, original_root, original_args[1:]), end)), changed
        # Unsupported root computations keep their exact source meaning. This
        # fallback is explicit and the proof must establish its full roundtrip.
        transformed, proof, original = value(t, root_fallback=True)
        encoded = call(layout['encode'][index], [transformed])
        return encoded, lift(proof, call(layout['encode'][index], [var('column_hole')])), original

    def law_term(index, operation, r, args):
        law = objects[layout['operation_laws'][index][operation]]['payload']['declaration']['Theorem']
        return sub(law['to'], dict(zip([n for n, _ in law['params']], [r, *args])))

    def value(t, root_fallback=False):
        for index, name in enumerate(roots):
            if t == var(name):
                decoded = call(layout['decode'][index], [var(names[index])])
                return decoded, use(layout['roundtrips'][index], [source_roots[index]]), source_roots[index]
        if not isinstance(t, dict):
            raise ValueError('column execution expects a term')
        for name,read in layout.get('ordered',{}).items():
            source_reply=model['actions'][name]['case']['normal']['Construct']['arguments'][0]
            if t==source_reply:
                source_root=source_roots[0]
                law=objects[layout['ordered_laws'][name]]['payload']['declaration']['Theorem']
                start=sub(law['from'],{'view_rows':source_root})
                proof=trans(convert(call(read,[encoded_roots[0]]),start),use(layout['ordered_laws'][name],[source_root]))
                return call(read,[var(names[0])]),proof,sub(source_reply,dict(zip(roots,source_roots)))
        if 'Call' in t:
            c = t['Call']
            for index, table in enumerate(model['tables']):
                if c['function'] in [table['get'], table['contains']]:
                    r, rp, logical = root(c['arguments'][0], index)
                    key, kp, source_key = value(c['arguments'][1])
                    direct = call(layout['points'][index], [r, key])
                    start_args = [sub(r, facts), sub(key, facts)]
                    end_args = [call(layout['encode'][index], [logical]), source_key]
                    point_proof = trans(*arguments(end_args, start_args, [rp, kp],
                        lambda xs: call(layout['points'][index], xs)),
                        use(layout['point_laws'][index], [logical, source_key]))
                    if c['function'] == table['get']:
                        return direct, point_proof, call(table['get'], [logical, source_key])
                    function = objects[table['contains']]['payload']['declaration']['Function']
                    body = sub(function['body'], dict(zip([n for n, _ in function['params']], [logical, source_key])))
                    get = call(table['get'], [logical, source_key])
                    context = replace(body, get, var('column_hole'))
                    return replace(body, get, direct), trans(lift(point_proof, context),
                        convert(body, call(table['contains'], [logical, source_key]))), call(table['contains'], [logical, source_key])
                if not root_fallback and c['function'] in [table[n] for n in ['insert', 'remove', 'replace']]:
                    r, rp, logical = root(t, index)
                    decoded = call(layout['decode'][index], [r])
                    return decoded, trans(lift(rp, call(layout['decode'][index], [var('column_hole')])),
                        use(layout['roundtrips'][index], [logical])), logical
            vals = [value(a) for a in c['arguments']]
            physical = call(c['function'], [a for a, _, _ in vals])
            original = call(c['function'], [a for _, _, a in vals])
            proof = trans(*arguments([a for _, _, a in vals], [sub(a, facts) for a, _, _ in vals],
                                    [p for _, p, _ in vals], lambda xs: call(c['function'], xs)), convert(original, original))
            return physical, proof, original
        if 'Construct' in t:
            c = t['Construct']; vals = [value(a) for a in c['arguments']]
            build = lambda xs: cons(c['datatype'], c['constructor'], xs)
        elif 'Binary' in t:
            b = t['Binary']; vals = [value(b['left']), value(b['right'])]
            build = lambda xs: {'Binary': dict(op=b['op'], left=xs[0], right=xs[1])}
        elif 'If' in t:
            x = t['If']; vals = [value(x[k]) for k in ['condition', 'on_true', 'on_false']]
            build = lambda xs: {'If': dict(zip(['condition', 'on_true', 'on_false'], xs))}
        elif 'Match' in t:
            x = t['Match']; vals = [value(x['scrutinee']), *[value(b['body']) for b in x['branches']]]
            build = lambda xs: match(xs[0], [(b['bindings'], a) for b, a in zip(x['branches'], xs[1:])])
        else:
            original = sub(t, dict(zip(roots, source_roots)))
            return original, {'Refl': original}, original
        physical = build([a for a, _, _ in vals]); original = build([a for _, _, a in vals])
        proof = trans(*arguments([a for _, _, a in vals], [sub(a, facts) for a, _, _ in vals],
                                [p for _, p, _ in vals], build), convert(original, original))
        return physical, proof, original

    def state(t):
        c = t.get('Construct', {})
        if c.get('datatype') != model['state'] or c.get('constructor') != 0:
            raise ValueError('direct column execution needs a projected state tuple')
        vals = [root(t, i) for i, t in enumerate(c['arguments'])]
        physical = cons(physical_id, 0, [vals[i][0] for i in order] + extra)
        original = cons(model['state'], 0, [z for _, _, z in vals])
        encoded = cons(physical_id, 0, [call(layout['encode'][i], [vals[i][2]]) for i in order] + extra)
        ps = [vals[i][1] for i in order] + [{'Refl': x} for x in extra]
        proof = {'Construct': dict(datatype=physical_id, constructor=0, arguments=ps)}
        return physical, proof, original, encoded

    def canonical(t, pair):
        original = sub(t, dict(zip(roots, source_roots)))
        post = match(original, [(['r', 'c', 'v', 's', 'e'], var('s')), (['h', 'v', 's'], var('s'))])
        # The physical state encoder is supplied by the caller through an
        # ordinary function; no distribution rule is assumed by Convert.
        return cons(pair, 0, [call(layout['state_encode'], [post]), original])

    def shift(proof):
        if isinstance(proof, dict):
            if set(proof) == {'Hypothesis'}:
                return {'Hypothesis': proof['Hypothesis'] + 1}
            return {k: shift(v) for k, v in proof.items()}
        if isinstance(proof, list): return [shift(v) for v in proof]
        return proof

    def action_term(t, pair):
        if 'If' in t:
            x = t['If']; c, cp, cz = value(x['condition'])
            l, lp, lz = action_term(x['on_true'], pair)
            r, rp, rz = action_term(x['on_false'], pair)
            build = lambda xs: {'If': dict(condition=xs[0], on_true=xs[1], on_false=xs[2])}
            physical = build([c, l, r]); intermediate = build([cz, sub(l, facts), sub(r, facts)])
            original = canonical(t, pair)
            branches = {}
            for label, flag, child, child_proof, child_original in [
                ('on_true', True, sub(l, facts), lp, lz), ('on_false', False, sub(r, facts), rp, rz)]:
                premise = {'Hypothesis': 0}
                left_context = replace(intermediate, cz, var('column_hole'))
                right_context = replace(original, cz, var('column_hole'))
                reduced_left = replace(intermediate, cz, {'Bool': flag})
                reduced_right = replace(original, cz, {'Bool': flag})
                branches[label] = trans(lift(premise, left_context), convert(reduced_left, child), shift(child_proof),
                    convert(child_original, reduced_right), {'Sym': lift(premise, right_context)})
            split = {'BoolSplit': dict(condition=cz, **{'from': intermediate, 'to': original}, **branches)}
            return physical, trans(lift(cp, build([var('column_hole'), sub(l, facts), sub(r, facts)])), split), original
        c = t['Construct']; args = c['arguments']; state_index = 3 if c['constructor'] == 0 else 2
        p, pp, logical, encoded = state(args[state_index])
        observation, op, original_observation = value(t)
        result = cons(pair, 0, [p, observation]); original = cons(pair, 0, [encoded, original_observation])
        goal = canonical(t, pair)
        return result, trans({'Construct': dict(datatype=pair, constructor=0, arguments=[pp, op])}, convert(original, goal)), goal

    return action_term, names, facts
