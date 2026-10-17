"""Untrusted closed computation with ordinary per-call equality witnesses.

An explicit stack keeps data traversal separate from proof nesting. Computed
constructor fields are evaluated once; existing literal aliases stay shared.
Named call equations bound proof nesting. The kernel replays every proposed step.
"""
import json

from producers.action_replacement import call, cons, convert, var
from producers.fold_chunks import compose
from producers.point_delta import binding_names, free_variables, lift, normal, sub, variables


class ClosedEquations:
    def __init__(self, chunks):
        self.chunks = chunks
        self.calls = {}
        self.active = set()
        self.serial = 0

    def hole(self, term):
        occupied = variables(term) | binding_names(term)
        while True:
            name = 'closed_equation_hole_'+str(self.serial)
            self.serial += 1
            if name not in occupied: return name

    def conversion(self, left, right):
        """Author congruence before asking conversion to compute a whole call."""
        self.chunks.tick()
        if left == right:
            return {'Refl': left}
        for kind in ('Call', 'Construct'):
            if kind not in left or kind not in right:
                continue
            a, b = left[kind], right[kind]
            if ({key: value for key, value in a.items() if key != 'arguments'} ==
                    {key: value for key, value in b.items() if key != 'arguments'}
                    and len(a['arguments']) == len(b['arguments'])):
                return {kind: dict(a, arguments=[self.conversion(x, y)
                    for x, y in zip(a['arguments'], b['arguments'])])}
        if 'Binary' in left and 'Binary' in right and left['Binary']['op'] == right['Binary']['op']:
            a, b = left['Binary'], right['Binary']
            return {'Binary': dict(op=a['op'], left=self.conversion(a['left'], b['left']),
                                   right=self.conversion(a['right'], b['right']))}
        return convert(left, right)

    def factored(self, original, value, proof):
        if original == value: return value, {'Refl': original}
        pending = [(proof, 1)]
        while pending:
            self.chunks.tick()
            current, depth = pending.pop()
            if depth > 6:
                theorem = self.chunks.theorem([], original, value, proof)
                return value, {'Use':dict(theorem=theorem,arguments=[],premises=[])}
            if 'Trans' in current: children = current['Trans']
            elif 'Sym' in current: children = [current['Sym']]
            elif 'Substitute' in current: children = [current['Substitute']['equality']]
            elif 'Call' in current: children = current['Call']['arguments']
            elif 'Construct' in current: children = current['Construct']['arguments']
            elif 'Binary' in current: children = [current['Binary']['left'],current['Binary']['right']]
            else: children = []
            pending.extend((child,depth+1)for child in children)
        return value, proof

    def evaluate(self, term):
        if free_variables(term):
            raise ValueError('closed computation has live inputs')
        tasks = [('eval', term)]
        values = []
        while tasks:
            self.chunks.tick()
            operation, node = tasks.pop()
            if operation == 'eval':
                if 'U64' in node or 'Bool' in node:
                    values.append((node, {'Refl': node}))
                elif 'Construct' in node:
                    tasks.append(('construct', node))
                    tasks.extend(('eval', argument) for argument in reversed(node['Construct']['arguments']))
                elif 'Call' in node:
                    invocation = node['Call']
                    function = self.chunks.objects[invocation['function']]['payload']['declaration'].get('Function')
                    if not function or len(function['params']) != len(invocation['arguments']):
                        raise ValueError('closed computation function/arity')
                    if not invocation['arguments'] and invocation['function'] in self.chunks.closed:
                        try:
                            self.chunks.expose(node)
                        except ValueError:
                            pass
                        else:
                            values.append((node, {'Refl': node})); continue
                    tasks.append(('apply', (node, function)))
                    tasks.extend(('eval', argument) for argument in reversed(invocation['arguments']))
                elif 'Binary' in node:
                    tasks.append(('binary', node))
                    tasks.extend([('eval', node['Binary']['right']), ('eval', node['Binary']['left'])])
                elif 'If' in node:
                    tasks.extend([('condition', node), ('eval', node['If']['condition'])])
                elif 'Match' in node:
                    tasks.extend([('scrutinee', node), ('eval', node['Match']['scrutinee'])])
                else:
                    raise ValueError('unsupported closed computation term')
            elif operation == 'apply':
                original, function = node
                count = len(function['params'])
                results = values[-count:] if count else []
                if count: del values[-count:]
                arguments = [value for value, _ in results]
                invocation = call(original['Call']['function'], arguments)
                congruence = {'Call': dict(function=original['Call']['function'], arguments=[p for _, p in results])}
                key = json.dumps(invocation, sort_keys=True, separators=(',', ':'))
                if key in self.calls:
                    value, theorem = self.calls[key]
                    values.append(self.factored(original, value, compose([congruence,
                        {'Use': dict(theorem=theorem, arguments=[], premises=[])}])))
                    continue
                if key in self.active: raise ValueError('closed computation call cycle')
                self.active.add(key)
                def self_calls(value):
                    if isinstance(value, dict):
                        if 'SelfCall' in value:
                            return call(original['Call']['function'], [self_calls(t) for t in value['SelfCall']])
                        return {k:self_calls(v) for k,v in value.items()}
                    if isinstance(value, list): return [self_calls(v) for v in value]
                    return value
                body = sub(self_calls(function['body']), dict(zip([n for n,_ in function['params']], arguments)))
                # Expose constructor/control redexes before writing a witness.
                # Named computations stay opaque. One checked conversion can
                # discard unused source arms instead of copying them into
                # every closed-call equation.
                body = normal(body, self.chunks.objects, opaque=set(self.chunks.objects),
                              heads=self.chunks.closed, tick=self.chunks.tick)
                opening = self.conversion(invocation, body)
                function_key = original['Call']['function']
                if function_key in self.chunks.folds:
                    rows = self.chunks.expose(arguments[0])['Construct']
                    if rows['constructor'] == 1:
                        # Instantiate one universal traversal step before
                        # simplifying the accumulator. A closed conversion of
                        # the whole call can otherwise evaluate its continuation
                        # repeatedly just to expose this single step.
                        head, tail = rows['arguments']
                        _, head_name, tail_name, step = self.chunks.folds[function_key]
                        bindings = dict(zip([name for name, _ in function['params'][1:]], arguments[1:]))
                        bindings.update({head_name: head, tail_name: tail})
                        raw = call(function_key, [tail, *arguments[1:-1], sub(step, bindings)])
                        exposed = call(function_key, [cons(rows['datatype'], 1, [head, tail]), *arguments[1:]])
                        opening = compose([self.conversion(invocation, exposed),
                            {'Use': dict(theorem=self.chunks.cons_equation(function_key),
                                         arguments=[head, tail, *arguments[1:]], premises=[])},
                            self.conversion(raw, body)])
                tasks.extend([('call-result', (key, original, invocation, body, congruence, opening)), ('eval', body)])
            elif operation == 'construct':
                constructor = node['Construct']; count = len(constructor['arguments'])
                results = values[-count:] if count else []
                if count: del values[-count:]
                computed = cons(constructor['datatype'], constructor['constructor'], [v for v,_ in results])
                value = self.chunks.share_data(computed)
                proof = {'Construct':dict(datatype=constructor['datatype'],constructor=constructor['constructor'],
                    arguments=[p for _,p in results])}
                values.append(self.factored(node, value, compose([proof, convert(computed,value)])))
            elif operation == 'call-result':
                key, original, invocation, body, congruence, opening = node
                value, proof = values.pop()
                theorem = self.chunks.theorem([], invocation, value, compose([opening, proof]))
                self.calls[key] = value, theorem
                self.active.remove(key)
                values.append(self.factored(original, value, compose([congruence,
                    {'Use': dict(theorem=theorem, arguments=[], premises=[])}])))
            elif operation == 'binary':
                right, right_proof = values.pop(); left, left_proof = values.pop()
                expression = {'Binary': dict(op=node['Binary']['op'], left=left, right=right)}
                value = normal(expression, self.chunks.objects, opaque=set(self.chunks.objects))
                if 'Binary' in value:
                    op = node['Binary']['op']
                    if op in ('quot','rem') and 'U64' in left and 'U64' in right:
                        value = {'U64': (left['U64']//right['U64'] if op=='quot' else left['U64']%right['U64']) if right['U64'] else 0}
                    else: raise ValueError('unsupported closed computation primitive')
                values.append(self.factored(node, value, compose([
                    {'Binary': dict(op=node['Binary']['op'], left=left_proof, right=right_proof)},
                    convert(expression, value)])))
            elif operation == 'condition':
                value, equality = values.pop()
                if 'Bool' not in value: raise ValueError('closed condition is not Boolean')
                source = node['If']; hole = self.hole(node)
                chosen = source['on_true' if value['Bool'] else 'on_false']
                context = {'If':dict(source, condition=var(hole))}
                reduced = {'If':dict(source, condition=value)}
                tasks.extend([('finish', (node,[lift(equality, context, hole), convert(reduced, chosen)])), ('eval', chosen)])
            elif operation == 'scrutinee':
                value, equality = values.pop()
                exposed = self.chunks.expose(value)
                constructor = exposed['Construct']; source = node['Match']
                branch = source['branches'][constructor['constructor']]
                if len(branch['bindings']) != len(constructor['arguments']):
                    raise ValueError('closed match arity')
                chosen = sub(branch['body'], dict(zip(branch['bindings'], constructor['arguments'])))
                hole = self.hole(node)
                context = {'Match':dict(source, scrutinee=var(hole))}
                reduced = {'Match':dict(source, scrutinee=value)}
                tasks.extend([('finish', (node,[lift(equality, context, hole), convert(reduced, chosen)])), ('eval', chosen)])
            elif operation == 'finish':
                value, proof = values.pop()
                original, prefix = node
                values.append(self.factored(original, value, compose([*prefix, proof])))
        if len(values) != 1: raise ValueError('closed computation result stack')
        return values[0]
