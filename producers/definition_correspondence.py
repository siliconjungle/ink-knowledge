"""Untrusted structural proofs relating separately named total definitions.

Alpha/shape matching proposes correspondence only. Every imported definition and
universal equality still replays in the ordinary first-order checker.
"""
from producers.action_replacement import call, cons, convert, var
from producers.equational import fresh_alpha
from producers.fold_chunks import compose
from producers.point_delta import lift, normal, replace, sub, variables


class DefinitionCorrespondence:
    def __init__(self, chunks):
        self.chunks = chunks
        self.cache = {}
        self.active = set()
        self.serial = 0

    def fresh(self, occupied):
        while True:
            name = 'correspondence_'+str(self.serial); self.serial += 1
            if name not in occupied:
                return name

    def function(self, key):
        return self.chunks.objects[key]['payload'].get('declaration', {}).get('Function')

    def discover(self, a, z):
        self.chunks.tick()
        if type(a) is not type(z):
            raise ValueError('definition correspondence shape')
        if isinstance(a, dict):
            if a.keys() != z.keys():
                raise ValueError('definition correspondence shape')
            if 'Call' in a:
                x, y = a['Call'], z['Call']
                if x['function'] != y['function']:
                    self.bridge(x['function'], y['function'])
                self.discover(x['arguments'], y['arguments'])
            else:
                for key in a:
                    self.discover(a[key], z[key])
        elif isinstance(a, list):
            if len(a) != len(z):
                raise ValueError('definition correspondence arity')
            for x, y in zip(a, z):
                self.discover(x, y)
        elif a != z:
            raise ValueError('definition correspondence differs')

    def bridge(self, first, second):
        key = first, second
        if key in self.cache:
            return self.cache[key]
        if key in self.active or len(self.active) >= self.chunks.MAX_DEPTH:
            raise ValueError('definition correspondence cycle/depth')
        f, g = self.function(first), self.function(second)
        if (not f or not g or f['result'] != g['result'] or f['recursive'] != g['recursive']
                or [t for _, t in f['params']] != [t for _, t in g['params']]):
            raise ValueError('definition correspondence signature')
        self.active.add(key)
        try:
            params = [['correspondence_arg_'+str(i), ty] for i, (_, ty) in enumerate(f['params'])]
            args = [var(n) for n, _ in params]
            def body(definition):
                return fresh_alpha(sub(definition['body'], dict(zip([n for n, _ in definition['params']], args))),
                                   {n: n for n, _ in params})
            left, right = body(f), body(g)
            self.discover(left, right)
            a, z = call(first, args), call(second, args)
            env = dict(params)
            if f['recursive'] is None:
                proof = compose([convert(a, left), self.terms(left, right, env, {}, {}, 0), convert(right, z)])
            else:
                index = f['recursive']; variable, sort = params[index]
                if not isinstance(sort, dict) or 'Data' not in sort:
                    raise ValueError('definition correspondence induction sort')
                datatype = sort['Data']
                constructors = self.chunks.objects[datatype]['payload']['declaration']['Datatype']['constructors']
                cases = []
                for ordinal, constructor in enumerate(constructors):
                    occupied = set(env) | variables(left) | variables(right); bindings = []
                    for _ in constructor['fields']:
                        name = self.fresh(occupied); occupied.add(name); bindings.append(name)
                    value = cons(datatype, ordinal, [var(n) for n in bindings])
                    local = {**env, **{n: sort if ty == 'SelfType' else ty
                              for n, ty in zip(bindings, constructor['fields'])}}
                    recursive = {n: i for i, n in enumerate(n for n, ty in zip(bindings, constructor['fields'])
                                                           if ty == 'SelfType')}
                    aa, zz = sub(a, {variable: value}), sub(z, {variable: value})
                    def open_body(term, function):
                        if isinstance(term, dict):
                            if 'SelfCall' in term:
                                return call(function, [open_body(t, function) for t in term['SelfCall']])
                            return {k: open_body(t, function) for k, t in term.items()}
                        if isinstance(term, list):
                            return [open_body(t, function) for t in term]
                        return term
                    l = sub(open_body(left, first), {variable: value})
                    r = sub(open_body(right, second), {variable: value})
                    scope = dict(first=first, second=second, index=index)
                    equality = self.terms(l, r, local, scope, recursive, 0)
                    cases.append(dict(bindings=bindings, proof=compose([convert(aa, l), equality, convert(r, zz)])))
                proof = {'GeneralizedInduction': dict(variable=variable,
                    generalize=[n for i, (n, _) in enumerate(params) if i != index],
                    **{'from': a, 'to': z}, cases=cases)}
            result = self.chunks.theorem(params, a, z, proof)
            self.cache[key] = result
            return result
        finally:
            self.active.remove(key)

    def terms(self, a, z, env, scope, recursive, hypotheses, depth=0):
        self.chunks.tick()
        if depth > 24:
            raise ValueError('definition correspondence term depth')
        # Only explicit constructors reduce here. All named calls stay opaque;
        # imported equalities and the current induction schema justify changes.
        opaque = set(self.chunks.objects)
        left = fresh_alpha(normal(a, self.chunks.objects, opaque=opaque), {n: n for n in env})
        right = fresh_alpha(normal(z, self.chunks.objects, opaque=opaque), {n: n for n in env})
        def done(proof):
            return compose([*([convert(a, left)] if a != left else []), proof,
                            *([convert(right, z)] if right != z else [])])
        if left == right:
            return done({'Refl': left})
        recur = lambda x, y, local=env, count=hypotheses: self.terms(x, y, local, scope, recursive, count, depth+1)
        if 'Call' in left and 'Call' in right:
            x, y = left['Call'], right['Call']
            if len(x['arguments']) != len(y['arguments']):
                raise ValueError('definition correspondence call arity')
            arguments = [recur(v, w) for v, w in zip(x['arguments'], y['arguments'])]
            congruence = {'Call': dict(function=x['function'], arguments=arguments)}
            if x['function'] == y['function']:
                return done(congruence)
            if scope and (x['function'], y['function']) == (scope['first'], scope['second']):
                subject = y['arguments'][scope['index']]
                if 'Var' not in subject or subject['Var'] not in recursive:
                    raise ValueError('definition correspondence recursion is not an immediate constructor field')
                equality = {'GeneralizedHypothesis': dict(index=recursive[subject['Var']],
                    arguments=[arg for i, arg in enumerate(y['arguments']) if i != scope['index']])}
            else:
                equality = {'Use': dict(theorem=self.bridge(x['function'], y['function']),
                                        arguments=y['arguments'], premises=[])}
            return done(compose([congruence, equality]))
        if 'Construct' in left and 'Construct' in right:
            x, y = left['Construct'], right['Construct']
            if (x['datatype'], x['constructor']) == (y['datatype'], y['constructor']):
                if len(x['arguments']) != len(y['arguments']):
                    raise ValueError('definition correspondence constructor arity')
                return done({'Construct': dict(datatype=x['datatype'], constructor=x['constructor'],
                    arguments=[recur(v, w) for v, w in zip(x['arguments'], y['arguments'])])})
        if 'Binary' in left and 'Binary' in right and left['Binary']['op'] == right['Binary']['op']:
            x, y = left['Binary'], right['Binary']
            return done({'Binary': dict(op=x['op'], left=recur(x['left'], y['left']), right=recur(x['right'], y['right']))})
        if 'If' in left and 'If' in right:
            x, y = left['If'], right['If']; hole = self.fresh(set(env) | variables(left) | variables(right))
            return done(compose([
                lift(recur(x['condition'], y['condition']), {'If': dict(condition=var(hole), on_true=x['on_true'], on_false=x['on_false'])}, hole),
                lift(recur(x['on_true'], y['on_true']), {'If': dict(condition=y['condition'], on_true=var(hole), on_false=x['on_false'])}, hole),
                lift(recur(x['on_false'], y['on_false']), {'If': dict(condition=y['condition'], on_true=y['on_true'], on_false=var(hole))}, hole)]))
        node = left.get('Match', right.get('Match'))
        if node:
            from producers.computation_equality import ComputationEquality
            sort = ComputationEquality(self.chunks).sort(node['scrutinee'], env)
            datatype = sort['Data']; cases = []
            constructors = self.chunks.objects[datatype]['payload']['declaration']['Datatype']['constructors']
            for ordinal, constructor in enumerate(constructors):
                occupied = set(env) | variables(left) | variables(right); names = []
                for _ in constructor['fields']:
                    name = self.fresh(occupied); occupied.add(name); names.append(name)
                value = cons(datatype, ordinal, [var(n) for n in names])
                local = {**env, **{n: {'Data': datatype} if ty == 'SelfType' else ty
                                  for n, ty in zip(names, constructor['fields'])}}
                hole = self.fresh(set(local) | variables(left) | variables(right))
                aa, zz = replace(left, node['scrutinee'], value), replace(right, node['scrutinee'], value)
                cases.append(dict(bindings=names, proof=compose([
                    lift({'Hypothesis': hypotheses}, replace(left, node['scrutinee'], var(hole)), hole),
                    recur(aa, zz, local, hypotheses+1),
                    {'Sym': lift({'Hypothesis': hypotheses}, replace(right, node['scrutinee'], var(hole)), hole)}])))
            return done({'Cases': dict(scrutinee=node['scrutinee'], **{'from': left, 'to': right}, cases=cases)})
        raise ValueError('definition correspondence has unmatched terms')
