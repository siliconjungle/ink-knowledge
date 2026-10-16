"""Untrusted ordinary lemmas composing closed traversals with typed helpers.

Discover matching structure, then propose a universal cons equation and bounded
chunk equations. No opcode, numeric identity, producer name or hash is authority.
The complete source-bound selection must replay every equation in the kernel.
"""
import json

from ink_knowledge import identity
from ink_knowledge.store import entry
from producers.action_replacement import MATH, alpha_normal, call, cons, convert, trans, var
from producers.point_delta import free_variables, lift, normal, sub


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

    def definition(self, params, result, body):
        declaration = {'Function': dict(params=params, recursive=None, result=result, body=body)}
        obj = entry('definition', MATH, {'declaration': declaration}, self.references(declaration),
                    parameters=dict(params), result=result)
        key = identity(obj); self.objects[key] = obj
        return key

    def consume(self, fold, rows, helper):
        """A reusable suffix-parametric prefix law plus a closed row witness.

        Prefix equations quantify over the unconsumed tail as well as all live
        arguments. The small closed witness binds this particular source list
        to that prefix. No proof depends on a cached producer verdict.
        """
        self.tick()
        key = ('consume', fold, json.dumps(rows, sort_keys=True, separators=(',', ':')), helper)
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
            list_type = f['params'][0][1]; datatype = list_type['Data']
            params = [['chunk_dynamic_'+str(i), t] for i, (_, t) in enumerate(f['params'][1:])]
            values = [var(n) for n, _ in params]; suffix = var('chunk_suffix')
            prefix_params = [['chunk_suffix', list_type]] + params
            invocation = call(helper, values)
            normalized = normal(sub(g['body'], dict(zip([n for n, _ in g['params']], values))),
                self.objects, opaque=self.helpers | self.closed, blocked=self.folds)
            right_call = normalized.get('Call', {}); right_helper = right_call.get('function')
            left_call = (right_call.get('arguments') or [{}])[-1].get('Call', {})
            left_helper = left_call.get('function')
            if right_helper in self.helpers and left_helper in self.helpers:
                if right_call['arguments'][:-1] != values[:-1] or left_call['arguments'] != values:
                    raise ValueError('fold chunk composition changes a capture')
                middle_rows, first, first_law, first_rows = self.consume(fold, rows, left_helper)
                remaining, second, second_law, second_rows = self.consume(fold, middle_rows, right_helper)
                template_key = ('prefix-pair', fold, helper, first, second)
                if template_key not in self.cache:
                    nested = call(first, [call(second, [suffix])])
                    builder = self.definition([['chunk_suffix', list_type]], list_type, nested)
                    middle = call(left_helper, values)
                    expanded = call(right_helper, [*values[:-1], middle])
                    left = call(fold, [call(builder, [suffix]), *values])
                    right = call(fold, [suffix, *values[:-1], invocation])
                    law = self.theorem(prefix_params, left, right, compose([
                        convert(left, call(fold, [nested, *values])),
                        {'Use': dict(theorem=first_law, arguments=[call(second,[suffix]),*values], premises=[])},
                        {'Use': dict(theorem=second_law, arguments=[suffix,*values[:-1],middle], premises=[])},
                        convert(call(fold,[suffix,*values[:-1],expanded]),right),
                    ]))
                    self.cache[template_key] = builder, law
                builder, law = self.cache[template_key]
                nested = call(first, [call(second,[remaining])])
                witness = self.theorem([], rows, call(builder,[remaining]), compose([
                    {'Use': dict(theorem=first_rows, arguments=[], premises=[])},
                    lift({'Use': dict(theorem=second_rows, arguments=[], premises=[])},
                         call(first,[var('chunk_rows_hole')]), 'chunk_rows_hole'),
                    convert(nested, call(builder,[remaining])),
                ]))
            else:
                if self.references(normalized) & self.helpers:
                    raise ValueError('fold chunk has unsupported helper composition')
                current, accumulator, heads, matched = rows, values[-1], [], None
                for count in range(self.MAX_CHUNK+1):
                    self.tick()
                    if count and alpha_normal(accumulator) == alpha_normal(normalized):
                        matched = current, list(heads)
                    if count == self.MAX_CHUNK:
                        break
                    node = self.expose(current)['Construct']
                    if node['constructor'] == 0 and not node['arguments']:
                        break
                    if node['constructor'] != 1 or len(node['arguments']) != 2:
                        raise ValueError('fold chunk has no matching bounded computation')
                    head, current = node['arguments']; heads.append(head)
                    bindings = dict(zip([n for n,_ in f['params'][1:]], [*values[:-1],accumulator]))
                    bindings.update({head_name:head,tail_name:current})
                    accumulator = normal(sub(step,bindings),self.objects,
                        opaque=self.helpers|self.closed,blocked=self.folds)
                if matched is None:
                    raise ValueError('fold chunk has no matching bounded computation')
                remaining, heads = matched
                template_key = ('prefix-leaf',fold,helper,json.dumps(heads,sort_keys=True,separators=(',',':')))
                if template_key not in self.cache:
                    prefix = suffix
                    for head in reversed(heads): prefix = cons(datatype,1,[head,prefix])
                    builder = self.definition([['chunk_suffix',list_type]],list_type,prefix)
                    left = call(fold,[call(builder,[suffix]),*values])
                    proofs = [convert(left,call(fold,[prefix,*values]))]
                    current, accumulator = prefix, values[-1]
                    cons_law = self.cons_equation(fold)
                    for head in heads:
                        tail = current['Construct']['arguments'][1]
                        proofs.append({'Use':dict(theorem=cons_law,
                            arguments=[head,tail,*values[:-1],accumulator],premises=[])})
                        bindings = dict(zip([n for n,_ in f['params'][1:]], [*values[:-1],accumulator]))
                        bindings.update({head_name:head,tail_name:tail})
                        raw = sub(step,bindings)
                        simplified = normal(raw,self.objects,opaque=self.helpers|self.closed,blocked=self.folds)
                        proofs.append(convert(call(fold,[tail,*values[:-1],raw]),call(fold,[tail,*values[:-1],simplified])))
                        current, accumulator = tail, simplified
                    right = call(fold,[suffix,*values[:-1],invocation])
                    proofs.append(convert(call(fold,[suffix,*values[:-1],accumulator]),right))
                    law = self.theorem(prefix_params,left,right,compose(proofs))
                    self.cache[template_key] = builder, law
                builder, law = self.cache[template_key]
                witness = self.theorem([],rows,call(builder,[remaining]),convert(rows,call(builder,[remaining])))
            result = remaining, builder, law, witness
            self.cache[key] = result
            return result
        finally:
            self.active.remove(key)

    def bridge(self, fold, rows, helper):
        remaining, builder, prefix, witness = self.consume(fold, rows, helper)
        exposed = self.expose(remaining)['Construct']
        if exposed['constructor'] != 0 or exposed['arguments']:
            raise ValueError('fold chunk composition does not consume every row')
        f = self.folds[fold][0]
        params = [['chunk_dynamic_'+str(i), t] for i, (_, t) in enumerate(f['params'][1:])]
        values = [var(n) for n,_ in params]
        left, right = call(fold,[rows,*values]),call(helper,values)
        proof = compose([
            lift({'Use':dict(theorem=witness,arguments=[],premises=[])},
                 call(fold,[var('chunk_rows_hole'),*values]),'chunk_rows_hole'),
            {'Use':dict(theorem=prefix,arguments=[remaining,*values],premises=[])},
            convert(call(fold,[remaining,*values[:-1],right]),right),
        ])
        return self.theorem(params,left,right,proof)
