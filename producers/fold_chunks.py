"""Untrusted ordinary lemmas composing closed traversals with typed helpers.

Discover matching structure, then propose a universal cons equation and bounded
chunk equations. No opcode, numeric identity, producer name or hash is authority.
The complete source-bound selection must replay every equation in the kernel.
"""
import json

from ink_knowledge import identity
from ink_knowledge.store import entry
from producers.action_replacement import MATH, alpha_normal, call, cons, convert, trans, var
from producers.point_delta import free_variables, normal, sub


def compose(proofs):
    """Balance ordinary transitivity; do not deepen a chunk with its step count."""
    if len(proofs) == 1:
        return proofs[0]
    middle = len(proofs) // 2
    return {'Trans': [compose(proofs[:middle]), compose(proofs[middle:])]}


class FoldChunks:
    MAX_WORK = 100_000
    MAX_CHUNK = 8
    MAX_HELPERS = 128
    MAX_DEPTH = 16

    def __init__(self, objects, helpers):
        self.objects = dict(objects)
        self.helpers = set(helpers)
        self.lemmas = set()
        self.work = 0
        self.active = set()
        self.cache = {}
        self.data_cache = {}
        self.folds = {}
        self.closed = set()
        for key, obj in self.objects.items():
            f = obj['payload'].get('declaration', {}).get('Function')
            if not f:
                continue
            if not f['params'] and f['recursive'] is None:
                self.closed.add(key)
            if f['recursive'] != 0 or len(f['params']) < 2 or 'Match' not in f['body']:
                continue
            m = f['body']['Match']; branches = m['branches']; params = f['params']
            if (m['scrutinee'] != var(params[0][0]) or len(branches) != 2
                    or branches[0]['bindings'] or branches[0]['body'] != var(params[-1][0])
                    or len(branches[1]['bindings']) != 2 or 'SelfCall' not in branches[1]['body']
                    or f['result'] != params[-1][1]):
                continue
            head, tail = branches[1]['bindings']; args = branches[1]['body']['SelfCall']
            if (len(args) != len(params) or args[0] != var(tail)
                    or args[1:-1] != [var(n) for n, _ in params[1:-1]]):
                continue
            self.folds[key] = (f, head, tail, args[-1])

    def tick(self):
        self.work += 1
        if self.work > self.MAX_WORK:
            raise ValueError('fold chunk proposal work budget')

    def references(self, term):
        pending = [term]; found = set(); seen = set()
        while pending:
            self.tick(); value = pending.pop()
            # Authoring constructs immutable DAGs: the same accumulator occurs
            # in several proof endpoints. Visit each live container once within
            # this synchronous walk; no cache survives it or stores verdicts.
            if isinstance(value, (dict, list)):
                if id(value) in seen:
                    continue
                seen.add(id(value))
            if isinstance(value, dict):
                for key in ['Data', 'datatype', 'function', 'theorem']:
                    name = value.get(key)
                    if isinstance(name, str) and name in self.objects:
                        found.add(name)
                pending.extend(value.values())
            elif isinstance(value, list):
                pending.extend(value)
        return found

    def theorem(self, params, left, right, proof):
        declaration = {'Theorem': dict(params=params, conditions=[],
            **{'from': left, 'to': right}, proof=proof)}
        obj = entry('theorem', MATH, {'declaration': declaration}, self.references(declaration),
                    parameters=dict(params))
        key = identity(obj); self.objects[key] = obj; self.lemmas.add(key)
        return key

    def expose(self, rows):
        seen = set()
        while 'Call' in rows:
            self.tick(); invocation = rows['Call']; key = invocation['function']
            if invocation['arguments'] or key not in self.closed or key in seen:
                raise ValueError('fold chunk requires closed constructor rows')
            seen.add(key)
            rows = self.objects[key]['payload']['declaration']['Function']['body']
        if 'Construct' not in rows:
            raise ValueError('fold chunk requires constructor rows')
        return rows

    def share(self, term):
        """Factor closed constructor depth into transparent ordinary definitions."""
        if free_variables(term):
            raise ValueError('fold chunk sharing requires closed data')
        def visit(value):
            self.tick()
            if 'Construct' not in value:
                return value, 0
            node = value['Construct']
            children = [visit(a) for a in node['arguments']]
            result = cons(node['datatype'], node['constructor'], [a for a, _ in children])
            height = 1 + max((h for _, h in children), default=0)
            if height <= 4:
                return result, height
            fingerprint = json.dumps(result, sort_keys=True, separators=(',', ':'))
            if fingerprint not in self.data_cache:
                declaration = {'Function': dict(params=[], recursive=None,
                    result={'Data': node['datatype']}, body=result)}
                obj = entry('definition', MATH, {'declaration': declaration}, self.references(declaration),
                            result={'Data': node['datatype']})
                key = identity(obj); self.objects[key] = obj; self.closed.add(key)
                self.data_cache[fingerprint] = key
            return call(self.data_cache[fingerprint], []), 0
        result, _ = visit(term)
        lemma = self.theorem([], term, result, convert(term, result))
        return result, lemma

    def cons_equation(self, fold):
        cached = self.cache.get(('cons', fold))
        if cached:
            return cached
        f, head, tail, body = self.folds[fold]
        datatype = f['params'][0][1]['Data']
        constructors = self.objects[datatype]['payload']['declaration']['Datatype']['constructors']
        if (len(constructors) != 2 or constructors[0]['fields']
                or len(constructors[1]['fields']) != 2
                or constructors[1]['fields'][1] not in ['SelfType', {'Data': datatype}]):
            raise ValueError('fold chunk list shape')
        params = [['chunk_head', constructors[1]['fields'][0]], ['chunk_tail', {'Data': datatype}]]
        params += [['chunk_dynamic_'+str(i), ty] for i, (_, ty) in enumerate(f['params'][1:])]
        values = [var(n) for n, _ in params]
        bindings = {head: values[0], tail: values[1]}
        bindings.update({n: v for (n, _), v in zip(f['params'][1:], values[2:])})
        left = call(fold, [cons(datatype, 1, values[:2]), *values[2:]])
        right = call(fold, [values[1], *values[2:-1], sub(body, bindings)])
        key = self.theorem(params, left, right, convert(left, right))
        self.cache[('cons', fold)] = key
        return key

    def consume(self, fold, rows, helper):
        """Prove a helper consumes a prefix, retaining its exact remaining fold."""
        self.tick()
        key = (fold, json.dumps(rows, sort_keys=True, separators=(',', ':')), helper)
        if key in self.cache:
            return self.cache[key]
        if key in self.active or len(self.active) >= self.MAX_DEPTH:
            raise ValueError('fold chunk helper depth/cycle budget')
        self.active.add(key)
        try:
            f, head_name, tail_name, step = self.folds[fold]
            g = self.objects[helper]['payload']['declaration']['Function']
            if (helper not in self.helpers or g['recursive'] is not None
                    or [t for _, t in g['params']] != [t for _, t in f['params'][1:]]
                    or g['result'] != f['result']):
                raise ValueError('fold chunk helper signature')
            params = [['chunk_dynamic_'+str(i), t] for i, (_, t) in enumerate(f['params'][1:])]
            values = [var(n) for n, _ in params]
            invocation = call(helper, values)
            left = call(fold, [rows, *values])
            normalized = normal(sub(g['body'], dict(zip([n for n, _ in g['params']], values))),
                self.objects, opaque=self.helpers | self.closed, blocked=self.folds)
            right_call = normalized.get('Call', {})
            right_helper = right_call.get('function')
            left_call = (right_call.get('arguments') or [{}])[-1].get('Call', {})
            left_helper = left_call.get('function')
            if right_helper in self.helpers and left_helper in self.helpers:
                if (right_call['arguments'][:-1] != values[:-1] or left_call['arguments'] != values):
                    raise ValueError('fold chunk composition changes a capture')
                middle_rows, left_lemma = self.consume(fold, rows, left_helper)
                remaining_rows, right_lemma = self.consume(fold, middle_rows, right_helper)
                middle = call(left_helper, values)
                expanded = call(right_helper, [*values[:-1], middle])
                proofs = [
                    {'Use': dict(theorem=left_lemma, arguments=values, premises=[])},
                    {'Use': dict(theorem=right_lemma, arguments=[*values[:-1], middle], premises=[])},
                    convert(call(fold, [remaining_rows, *values[:-1], expanded]),
                            call(fold, [remaining_rows, *values[:-1], invocation])),
                ]
            else:
                if self.references(normalized) & self.helpers:
                    raise ValueError('fold chunk has unsupported helper composition')
                current_rows, accumulator, proofs = rows, values[-1], []
                cons_lemma = self.cons_equation(fold)
                for count in range(self.MAX_CHUNK + 1):
                    self.tick()
                    if count and alpha_normal(accumulator) == alpha_normal(normalized):
                        remaining_rows = current_rows
                        proofs.append(convert(call(fold, [current_rows, *values[:-1], accumulator]),
                                              call(fold, [current_rows, *values[:-1], invocation])))
                        break
                    exposed = self.expose(current_rows); node = exposed['Construct']
                    if count == self.MAX_CHUNK or node['constructor'] != 1 or len(node['arguments']) != 2:
                        raise ValueError('fold chunk has no matching bounded computation')
                    head, tail = node['arguments']
                    old = call(fold, [current_rows, *values[:-1], accumulator])
                    exposed_call = call(fold, [exposed, *values[:-1], accumulator])
                    proofs.append(convert(old, exposed_call))
                    proofs.append({'Use': dict(theorem=cons_lemma,
                        arguments=[head, tail, *values[:-1], accumulator], premises=[])})
                    bindings = dict(zip([n for n, _ in f['params'][1:]], [*values[:-1], accumulator]))
                    bindings.update({head_name: head, tail_name: tail})
                    raw = sub(step, bindings)
                    simplified = normal(raw, self.objects, opaque=self.helpers | self.closed, blocked=self.folds)
                    proofs.append(convert(call(fold, [tail, *values[:-1], raw]),
                                          call(fold, [tail, *values[:-1], simplified])))
                    current_rows, accumulator = tail, simplified
            right = call(fold, [remaining_rows, *values[:-1], invocation])
            lemma = self.theorem(params, left, right, compose(proofs))
            self.cache[key] = (remaining_rows, lemma)
            return remaining_rows, lemma
        finally:
            self.active.remove(key)

    def bridge(self, fold, rows, helper):
        remaining, prefix = self.consume(fold, rows, helper)
        exposed = self.expose(remaining)['Construct']
        if exposed['constructor'] != 0 or exposed['arguments']:
            raise ValueError('fold chunk composition does not consume every row')
        f = self.folds[fold][0]
        params = [['chunk_dynamic_'+str(i), t] for i, (_, t) in enumerate(f['params'][1:])]
        values = [var(n) for n, _ in params]
        left, right = call(fold, [rows, *values]), call(helper, values)
        proof = compose([{'Use':dict(theorem=prefix, arguments=values, premises=[])},
            convert(call(fold, [remaining, *values[:-1], right]), right)])
        return self.theorem(params, left, right, proof)
