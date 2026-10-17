"""Untrusted explicit definitional witnesses with live, opaque captures.

Small checked definition and selector steps preserve typed, opaque captures.
Every proposed equation still replays in the ordinary kernel.
"""
from producers.action_replacement import call, cons, convert, var
from producers.equational import fresh_alpha
from producers.fold_chunks import compose
from producers.point_delta import binding_names, free_variables, lift, normal, sub, variables


class OpenEquations:
    def __init__(self, chunks):
        self.chunks = chunks
        if not hasattr(chunks, 'constructor_equations'):
            from producers.constructor_equations import ConstructorEquations
            chunks.constructor_equations = ConstructorEquations(chunks)
        self.constructor_equations = chunks.constructor_equations
        self.serial = 0
        from producers.closed_equations import ClosedEquations
        self.closed = ClosedEquations(chunks)

    def fresh(self, term, prefix):
        occupied = variables(term) | binding_names(term)
        while True:
            name = prefix + str(self.serial)
            self.serial += 1
            if name not in occupied:
                return name

    def factor(self, left, right, proof, env):
        if left == right:
            return right, {'Refl': left}
        pending = [(proof, 0)]
        while pending:
            self.chunks.tick()
            value, depth = pending.pop()
            if depth > 5:
                names = sorted(free_variables([left, right]))
                params = [[name, env[name]] for name in names]
                if any(ty is None for _, ty in params):
                    raise ValueError('open equation needs typed free variables')
                key = self.chunks.theorem(params, left, right, proof)
                return right, {'Use': dict(theorem=key, arguments=[var(name) for name in names], premises=[])}
            children = []
            if 'Trans' in value:
                children = value['Trans']
            elif 'Sym' in value:
                children = [value['Sym']]
            elif 'Substitute' in value:
                children = [value['Substitute']['equality']]
            elif 'Call' in value:
                children = value['Call']['arguments']
            elif 'Construct' in value:
                children = value['Construct']['arguments']
            elif 'Binary' in value:
                children = [value['Binary']['left'], value['Binary']['right']]
            pending.extend((child, depth + 1) for child in children)
        return right, proof

    def expanded_body(self, function, body):
        if isinstance(body, dict):
            if 'SelfCall' in body:
                return call(function, [self.expanded_body(function, term) for term in body['SelfCall']])
            return {key: self.expanded_body(function, value) for key, value in body.items()}
        if isinstance(body, list):
            return [self.expanded_body(function, value) for value in body]
        return body

    def opening(self, invocation, env):
        name, arguments = invocation['function'], invocation['arguments']
        function = self.chunks.objects[name]['payload']['declaration']['Function']
        if len(function['params']) != len(arguments):
            raise ValueError('open equation function arity')
        if function['recursive'] is not None and 'Construct' not in arguments[function['recursive']]:
            raise ValueError('open equation recursive argument needs a constructor')
        body = fresh_alpha(sub(self.expanded_body(name, function['body']),
            dict(zip([n for n, _ in function['params']], arguments))), {name: name for name in env})
        return body, {'Step': call(name, arguments)}

    def beta(self, term, env):
        return self.constructor_equations.beta(term, env)

    def normalize(self, term, env, depth=0, control=False):
        self.chunks.tick()
        if depth > 64:
            raise ValueError('open equation normalization depth')
        def recur(value):
            return self.normalize(value, env, depth + 1, control)
        def finish(value, proof):
            return self.factor(term, value, proof, env)
        if 'Call' in term or 'Construct' in term:
            kind = 'Call' if 'Call' in term else 'Construct'
            node = term[kind]
            results = [recur(argument) for argument in node['arguments']]
            arguments = [value for value, _ in results]
            value = {kind: dict(node, arguments=arguments)}
            proof = {kind: dict(node, arguments=[p for _, p in results])}
            if kind == 'Construct':
                if not control and not free_variables(value):
                    shared = self.chunks.share_data(value)
                    return finish(shared, compose([proof, convert(value, shared)]))
                return finish(value, proof)
            if control:
                return finish(value, proof)
            function = self.chunks.objects[node['function']]['payload']['declaration'].get('Function')
            opaque = self.chunks.helpers | self.chunks.closed | self.chunks.gates | self.chunks.folds.keys()
            if function is None or node['function'] in opaque or not free_variables(arguments):
                return finish(value, proof)
            if function['recursive'] is not None:
                index = function['recursive']
                try:
                    exposed = self.chunks.expose(arguments[index])
                except ValueError:
                    return finish(value, proof)
                if 'Construct' not in exposed:
                    return finish(value, proof)
                if exposed != arguments[index]:
                    equalities = [{'Refl': argument} for argument in arguments]
                    equalities[index] = convert(arguments[index], exposed)
                    arguments[index] = exposed
                    proof = compose([proof, {'Call': dict(function=node['function'], arguments=equalities)}])
                    value = call(node['function'], arguments)
            body, opening = self.opening(value['Call'], env)
            result, continuation = recur(body)
            return finish(result, compose([proof, opening, continuation]))
        if 'Match' in term:
            node = term['Match']
            value, proof = recur(node['scrutinee'])
            hole = self.fresh(term, 'open_scrutinee_')
            proof = lift(proof, {'Match': dict(node, scrutinee=var(hole))}, hole)
            if not control and not free_variables(value):
                computed, equation = self.closed.evaluate(value)
                proof = compose([proof, lift(equation, {'Match': dict(node, scrutinee=var(hole))}, hole)])
                value = computed
            try:
                exposed = self.chunks.expose(value)
            except ValueError:
                exposed = value
            if exposed != value:
                proof = compose([proof, lift(convert(value, exposed), {'Match': dict(node, scrutinee=var(hole))}, hole)])
            value = exposed
            reduced = {'Match': dict(node, scrutinee=value)}
            if 'Construct' not in value:
                return finish(reduced, proof)
            constructor = value['Construct']
            branch = node['branches'][constructor['constructor']]
            body, opening = self.beta(reduced, env)
            result, continuation = recur(body)
            return finish(result, compose([proof, opening, continuation]))
        if 'If' in term:
            node = term['If']; condition, proof = recur(node['condition'])
            hole = self.fresh(term, 'open_condition_')
            proof = lift(proof, {'If': dict(node, condition=var(hole))}, hole)
            if not control and not free_variables(condition):
                computed, equation = self.closed.evaluate(condition)
                proof = compose([proof, lift(equation, {'If': dict(node, condition=var(hole))}, hole)])
                condition = computed
            reduced = {'If': dict(node, condition=condition)}
            if 'Bool' in condition:
                chosen = node['on_true' if condition['Bool'] else 'on_false']
                result, continuation = recur(chosen)
                return finish(result, compose([proof, convert(reduced, chosen), continuation]))
            first, p = recur(node['on_true']); second, q = recur(node['on_false'])
            result = {'If': dict(condition=condition, on_true=first, on_false=second)}
            return finish(result, compose([proof,
                lift(p, {'If': dict(condition=condition, on_true=var(hole), on_false=node['on_false'])}, hole),
                lift(q, {'If': dict(condition=condition, on_true=first, on_false=var(hole))}, hole)]))
        if 'Binary' in term:
            node = term['Binary']; left, first = recur(node['left']); right, second = recur(node['right'])
            value = {'Binary': dict(node, left=left, right=right)}
            proof = {'Binary': dict(op=node['op'], left=first, right=second)}
            if control:
                if all('U64' in part or 'Bool' in part for part in [left,right]):
                    result = normal(value,self.chunks.objects,opaque=set(self.chunks.objects))
                    return finish(result,compose([proof,convert(value,result)]))
                return finish(value,proof)
            if not free_variables(value):
                result, equation = self.closed.evaluate(value)
                return finish(result, compose([proof, equation]))
            return finish(value, proof)
        if 'Var' in term or 'U64' in term or 'Bool' in term:
            return term, {'Refl': term}
        raise ValueError('unsupported open equation term')
