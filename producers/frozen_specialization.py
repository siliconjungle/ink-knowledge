#!/usr/bin/env python3
"""Propose structural specialization from checked immutable application state.

This is bounded, untrusted partial evaluation. The ordinary compiler checks the
candidate source and replays complete action equalities. Training scores and this
producer's evaluation never authorize a replacement or establish profitability.
"""
import argparse
import copy
import json
import math
from pathlib import Path
import subprocess
import struct
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store
from producers.action_replacement import alpha_normal, call, cons, convert, trans, var
from producers.point_delta import equality, lift, normal, replace, sub
from producers.closed_data_bridges import ClosedDataBridges
from producers.fixed_f32 import evaluate as fixed_f32


def source_free(value, bound=frozenset()):
    if isinstance(value, list):
        return set().union(*(source_free(x, bound) for x in value)) if value else set()
    if not isinstance(value, dict):
        return set()
    if 'Var' in value:
        return {value['Var']} - bound
    if 'Lambda' in value:
        name, body = value['Lambda']; return source_free(body, bound | {name})
    if 'Let' in value:
        name, _, initial, body = value['Let']
        return source_free(initial, bound) | source_free(body, bound | {name})
    return set().union(*(source_free(x, bound) for x in value.values()))


def float_bits(value):
    if isinstance(value, dict):
        if set(value) == {'Float'}:
            return value['Float']
        if set(value) == {'Call'} and value['Call'][0] == 'f32_from_bits':
            args = value['Call'][1]
            if len(args) == 1 and isinstance(args[0], dict) and set(args[0]) == {'Num'}:
                bits = args[0]['Num']
                if type(bits) is int and 0 <= bits <= 0xffffffff:
                    return bits
    return None


def substitute(e, bindings):
    """Source expression substitution; fresh free names are supplied by Partial."""
    if isinstance(e, list):
        return [substitute(x, bindings) for x in e]
    if not isinstance(e, dict):
        return e
    if 'Var' in e:
        return copy.deepcopy(bindings.get(e['Var'], e))
    if 'Lambda' in e:
        n, body = e['Lambda']
        return {'Lambda': [n, substitute(body, {k: v for k, v in bindings.items() if k != n})]}
    if 'Let' in e:
        n, ty, value, body = e['Let']
        return {'Let': [n, ty, substitute(value, bindings),
                        substitute(body, {k: v for k, v in bindings.items() if k != n})]}
    return {k: substitute(x, bindings) for k, x in e.items()}


def literal(ty, value, program, depth=0):
    if depth > 32:
        raise ValueError('frozen literal depth budget')
    recur = lambda t, v: literal(t, v, program, depth+1)
    if ty in ('U32', 'U64') and type(value) is int:
        return {'Num': value}
    if ty == 'Bool' and type(value) is bool:
        return {'Bool': value}
    if ty == 'F32':
        if isinstance(value, dict) and set(value) == {'F32Bits'}:
            bits = value['F32Bits']
            if type(bits) is not int or not 0 <= bits <= 0xffffffff:
                raise ValueError('frozen F32 bits outside range')
        elif type(value) in (int, float):
            try:
                if not math.isfinite(value):
                    raise ValueError('non-finite frozen F32 requires exact bits')
                bits = int.from_bytes(struct.pack('>f', value), 'big')
            except (OverflowError, struct.error) as error:
                raise ValueError('frozen F32 outside finite range') from error
            if bits & 0x7f800000 == 0x7f800000:
                raise ValueError('frozen F32 outside finite range')
        else:
            raise ValueError('invalid frozen F32 value')
        # Float literals are finite in executable core. The ordinary bitcast
        # constructs exceptional values without canonicalizing their payloads.
        return ({'Call': ['f32_from_bits', [{'Num': bits}]]}
                if bits & 0x7f800000 == 0x7f800000 else {'Float': bits})
    if ty == 'Unit':
        return 'Unit'
    if isinstance(ty, dict):
        if 'Named' in ty:
            name = ty['Named']
            if name in program['enums'] and value in [name+'.'+v for v in program['enums'][name]]:
                return {'Field': [{'Var': name}, value[len(name)+1:]]}
            if name in program['records']:
                return {'Record': [name, [[n, recur(t, value[n])] for n, t in program['records'][name]]]}
        if 'Option' in ty:
            if value == {'None': None}:
                return {'Var': 'None'}
            return {'Call': ['Some', [recur(ty['Option'], value['Some'])]]}
        if 'Result' in ty:
            arm = 'Ok' if 'Ok' in value else 'Err'
            return {'Call': [arm, [recur(ty['Result'][arm == 'Err'], value[arm])]]}
        if 'List' in ty:
            return {'Call': ['list', [recur(ty['List'], x) for x in value]]}
    raise ValueError('unsupported frozen source literal')


class Partial:
    def __init__(self, program):
        self.program = program
        self.functions = {f['name']: f for f in program['functions']}
        self.roots = {s['name']: s['ty']['Table'] for s in program['states']}
        self.enums = {n+'.'+v for n, vs in program['enums'].items() for v in vs}
        self.work = 0
        self.serial = 0
        self.generated = set()
        self.types = {}
        self.contextual = set()
        self.source_text = json.dumps(program)

    def fresh(self):
        while True:
            name = '__frozen_proposal_'+str(self.serial)
            self.serial += 1
            if name not in self.source_text:
                self.generated.add(name)
                return name

    def tick(self, depth):
        self.work += 1
        if self.work > 100000 or depth > 64:
            raise ValueError('frozen specialization work budget')

    def value(self, e, *, equality=False):
        if e == 'Unit':
            return True
        if not isinstance(e, dict):
            return False
        if any(k in e for k in ('Num', 'Bool')):
            return True
        if 'Float' in e:
            return not equality
        if 'Var' in e:
            return e['Var'] in self.enums or e['Var'] == 'None'
        if 'Field' in e:
            base, field = e['Field']
            return isinstance(base, dict) and base.get('Var', '')+'.'+field in self.enums
        if 'Record' in e:
            return all(self.value(x, equality=equality) for _, x in e['Record'][1])
        if 'Call' in e:
            n, args = e['Call']
            if n == 'f32_from_bits' and len(args) == 1 and isinstance(args[0], dict) and set(args[0]) == {'Num'}:
                return not equality and type(args[0]['Num']) is int and 0 <= args[0]['Num'] <= 0xffffffff
            return n in ('Some', 'Ok', 'Err', 'list') and all(self.value(a, equality=equality) for a in args)
        return False

    def fold(self, name, args, active, depth):
        """Expand a closed traversal, keeping the accumulator in fresh slots.

        This is a proposal, not a new equality rule. Closed scalar arithmetic
        uses the integer-only fixed-primitive author; the ordinary transition
        proof must establish every step in its original operation order.
        """
        if len(args) != 3:
            return None
        rows, initial, step = args
        if (not isinstance(rows, dict) or rows.get('Call', [None])[0] != 'list'
                or not self.value(rows) or not isinstance(step, dict) or 'Lambda' not in step):
            return None
        element, inner = step['Lambda']
        if not isinstance(inner, dict) or 'Lambda' not in inner:
            return None
        accumulator, body = inner['Lambda']
        # The initializer executes once even for an empty list or an unused
        # accumulator. Each intermediate executes once, including when the
        # next step mentions its accumulator more than once or not at all.
        previous = self.fresh()
        bindings = [(previous, initial)]
        values = rows['Call'][1]
        for value in values if name == 'foldl' else reversed(values):
            self.tick(depth)
            following = self.fresh()
            expression = substitute(body, {element: value, accumulator: {'Var': previous}})
            bindings.append((following, self.expr(expression, {}, active, depth + 1)))
            previous = following
        result = {'Var': previous}
        for local, value in reversed(bindings):
            result = {'Let': [local, None, value, result]}
        return result

    def leading_bindings(self, expression, statements):
        # Only our globally fresh binders can move into the surrounding block.
        # User lexical scopes, operand positions and lazy branches stay intact.
        while isinstance(expression, dict) and 'Let' in expression:
            name, ty, value, body = expression['Let']
            if name not in self.generated:
                break
            statements.append({'Let': [name, ty, value]})
            expression = body
        return expression

    def preserve_result(self, residual, result):
        if isinstance(result, dict) and 'Result' in result:
            result_name = self.fresh()
            self.types[result_name] = result
            self.contextual.add(result_name)
            residual = {'Let': [result_name, result, residual, {'Var': result_name}]}
        return residual

    def should_inline(self, name, args, original):
        return any(self.value(x) for x in args)

    def scalar(self, op, left, right=None):
        a = float_bits(left); b = 0 if right is None else float_bits(right)
        if a is None or b is None:
            return None
        result = fixed_f32('f32:'+op, a, b)
        return result if result is None or 'Bool' in result else literal('F32', {'F32Bits': result['U64']}, self.program)

    def constant_call(self, name, args):
        if name == 'length' and len(args) == 1 and isinstance(args[0],dict) and self.value(args[0]) and args[0].get('Call', [None])[0] == 'list':
            return {'Num': len(args[0]['Call'][1]) & 0xffffffff}
        if name == 'f32_bits' and len(args) == 1:
            bits = float_bits(args[0])
            return None if bits is None else {'Num': bits}
        if name in ('f32_from_bits','f32_from_u32','f32_from_u64','f32_from_i32') and len(args) == 1:
            argument = args[0]; negative = name == 'f32_from_i32' and isinstance(argument, dict) and 'Neg' in argument
            if negative: argument = argument['Neg']
            limit = (1 << 64) if name == 'f32_from_u64' else (1 << 31) if name == 'f32_from_i32' else (1 << 32)
            if negative: limit += 1
            if isinstance(argument, dict) and set(argument) == {'Num'} and type(argument['Num']) is int and 0 <= argument['Num'] < limit:
                word = (-argument['Num'] if negative else argument['Num']) % (1 << 64)
                bits = word & 0xffffffff if name == 'f32_from_bits' else fixed_f32('f32:'+name[4:], word)['U64']
                return literal('F32', {'F32Bits': bits}, self.program)
        unary = {'sqrt','floor','ceil','trunc','round_ties_even','is_nan','is_finite'}
        if name in unary and len(args) == 1: return self.scalar(name,args[0])
        if name == 'f32_div' and len(args) == 2: return self.scalar('div',*args)
        return None

    def closed_map(self, base, callback, active, depth):
        if (not isinstance(base, dict) or base.get('Call',[None])[0] != 'list'
                or not self.value(base) or not isinstance(callback, dict) or 'Lambda' not in callback):
            return None
        name, body = callback['Lambda']
        if source_free(body,{name}) - self.enums - self.program['enums'].keys() - {'None'}:
            return None
        # A failed closed-value attempt must not retain speculative helper code
        # or lexical/type state. Its work still counts against the global budget.
        names = ['serial','generated','contextual','types','functions','helpers','helper_index','helper_names']
        snapshot = {key:copy.copy(getattr(self,key)) for key in names if hasattr(self,key)}
        values = []
        for value in base['Call'][1]:
            result = self.expr(substitute(body,{name:value}),{},active,depth+1)
            if not self.value(result):
                for key, saved in snapshot.items(): setattr(self,key,saved)
                return None
            values.append(result)
        return {'Call':['list',values]}

    def inline_call(self, function, args, active, depth):
        names = [self.fresh() for _ in args]
        for fresh, (_, ty) in zip(names, function['params']):
            self.types[fresh] = ty
        body = substitute(function['body'], {p[0]: {'Var': fresh} for p, fresh in zip(function['params'], names)})
        for fresh, (_, ty), value in reversed(list(zip(names, function['params'], args))):
            body = {'Let': [fresh, ty, value, body]}
        return self.preserve_result(self.expr(body, {}, active, depth+1), function['result'])

    def expr(self, e, env=None, active=(), depth=0):
        self.tick(depth)
        env = env or {}
        rec = lambda x: self.expr(x, env, active, depth+1)
        if not isinstance(e, dict):
            return e
        if 'Var' in e:
            return copy.deepcopy(env.get(e['Var'], e))
        if 'Let' in e:
            n, ty, value, body = e['Let']
            value = rec(value)
            local = {k: v for k, v in env.items() if k != n}
            if self.value(value) and n not in self.contextual:
                local[n] = value
                return self.expr(body, local, active, depth+1)
            return {'Let': [n, ty, value, self.expr(body, local, active, depth+1)]}
        if 'Lambda' in e:
            n, body = e['Lambda']
            return {'Lambda': [n, self.expr(body, {k: v for k, v in env.items() if k != n}, active, depth+1)]}
        if 'Field' in e:
            base, name = e['Field']
            base = rec(base)
            if self.value(base) and isinstance(base, dict) and 'Record' in base:
                return dict(base['Record'][1])[name]
            return {'Field': [base, name]}
        if 'Record' in e:
            n, fields = e['Record']
            return {'Record': [n, [[k, rec(x)] for k, x in fields]]}
        if 'Call' in e:
            n, args = e['Call']
            if n == 'choose' and len(args) == 3:
                condition = rec(args[0])
                if 'Bool' in condition:
                    return rec(args[1 if condition['Bool'] else 2])
                return {'Call': [n, [condition, rec(args[1]), rec(args[2])]]}
            args = [rec(x) for x in args]
            if n not in self.functions:
                value = self.constant_call(n,args)
                if value is not None:
                    return value
            if n in ('foldl', 'foldr'):
                folded = self.fold(n, args, active, depth)
                if folded is not None:
                    return folded
            # Bind every argument once in source order, under names fresh for
            # the complete source. Closed parameters can then expose branches
            # inside helpers without capturing or duplicating dynamic inputs.
            if n in self.functions and n not in active and len(active) < 16:
                f = self.functions[n]
                if len(args) == len(f['params']) and self.should_inline(n,args,e['Call'][1]):
                    return self.inline_call(f, args, (*active, n), depth+1)
            return {'Call': [n, args]}
        if 'Method' in e:
            base, name, args = e['Method']
            base = rec(base)
            args = [rec(x) for x in args]
            if name == 'map' and len(args) == 1:
                value = self.closed_map(base,args[0],active,depth)
                if value is not None: return value
            root = base.get('Var') if isinstance(base, dict) else None
            if root in self.program.get('frozen', {}) and name in ('get', 'contains') and len(args) == 1 and 'Num' in args[0]:
                keyty, valuety = self.roots[root]
                if keyty in ('U32', 'U64'):
                    row = next((v for k, v in self.program['frozen'][root] if k == args[0]['Num']), None)
                    present = any(k == args[0]['Num'] for k, _ in self.program['frozen'][root])
                    if name == 'contains':
                        return {'Bool': present}
                    if not present:
                        return {'Var': 'None'}
                    try:
                        return {'Call': ['Some', [literal(valuety, row, self.program)]]}
                    except (ValueError, KeyError, TypeError):
                        pass
            if name == 'unwrap_or' and len(args) == 1 and self.value(base) and self.value(args[0]):
                if base == {'Var': 'None'}:
                    return args[0]
                if isinstance(base, dict) and base.get('Call', [None])[0] == 'Some':
                    return base['Call'][1][0]
            return {'Method': [base, name, args]}
        if 'Binary' in e:
            op, a, z = e['Binary']
            a = rec(a)
            if op in ('&&', '||') and 'Bool' in a:
                return rec(z) if a['Bool'] == (op == '&&') else a
            z = rec(z)
            if op in ('+','-','*','==','!=','<','<=','>','>='):
                value = self.scalar(op,a,z)
                if value is not None: return value
            # Composite equality does not use Python syntax/raw-bit equality
            # for a value containing floats. Scalar IEEE proposals above are
            # separate and still need ordinary checked conversion.
            if op in ('==', '!=') and self.value(a, equality=True) and self.value(z, equality=True):
                return {'Bool': (a == z) == (op == '==')}
            return {'Binary': [op, a, z]}
        if 'Neg' in e or 'Try' in e:
            k = next(iter(e))
            value = rec(e[k])
            if k == 'Neg':
                folded = self.scalar('neg',value)
                if folded is not None: return folded
            return {k: value}
        return copy.deepcopy(e)

    def statements(self, statements, env=None):
        env = dict(env or {})
        result = []
        for statement in statements:
            if 'Let' in statement:
                n, ty, value = statement['Let']
                value = self.expr(value, env)
                env.pop(n, None)
                if self.value(value) and n not in self.contextual:
                    env[n] = value
                else:
                    value = self.leading_bindings(value, result)
                    result.append({'Let': [n, ty, value]})
            elif 'If' in statement:
                condition, yes, no = statement['If']
                condition = self.expr(condition, env)
                condition = self.leading_bindings(condition, result)
                if 'Bool' in condition:
                    result.extend(self.statements(yes if condition['Bool'] else no, env))
                else:
                    result.append({'If': [condition, self.statements(yes, env), self.statements(no, env)]})
            elif 'Emit' in statement:
                event, value = statement['Emit']
                value = self.leading_bindings(self.expr(value, env), result)
                result.append({'Emit': [event, value]})
            else:
                key = next(iter(statement))
                value = self.leading_bindings(self.expr(statement[key], env), result)
                result.append({key: value})
        return result


def specialize(source):
    selected = copy.deepcopy(source)
    partial = Partial(selected['program'])
    for action in selected['program']['actions']:
        action['body'] = partial.statements(action['body'])
    return selected


def compact_equality(a, z, state, frozen, objects, bridges=None):
    """Transport fixed rows without copying fully expanded arithmetic primals."""
    if alpha_normal(a['case']['normal']) == alpha_normal(z['case']['normal']):
        return convert(a['case']['call'], z['case']['call'])
    def rewrite(term):
        steps = []
        for index, equation in enumerate(frozen):
            left = sub(equation['from'], {'initial': state})
            right = sub(equation['to'], {'initial': state})
            exposed = normal(left, objects)
            context = replace(term, exposed, var('frozen_compact_hole'))
            if context == term:
                continue
            premise = trans({'Sym': convert(left, exposed)}, {'Hypothesis': index})
            steps.append(lift(premise, context, 'frozen_compact_hole'))
            term = replace(term, exposed, right)
        return term, steps
    def exposed(action):
        term = action['case']['normal']
        if bridges and bridges.aliases and term == action['case']['call']:
            # A bounded core hint may retain its call to preserve large data.
            # Expose that call while keeping every closed data alias opaque.
            term = normal(term, objects, opaque=bridges.opaque)
        return term
    left_hint, right_hint = exposed(a), exposed(z)
    left, forward = rewrite(left_hint)
    right, backward = rewrite(right_hint)
    if bridges and bridges.aliases:
        avoid = {n for action in (a,z) for n,_ in action['case']['params']}
        left, steps = bridges.rewrite(left, avoid)
        forward.extend(steps)
        right, steps = bridges.rewrite(right, avoid)
        backward.extend(steps)
    return trans(convert(a['case']['call'], left_hint), *forward,
                 convert(left, right), *[{'Sym': step} for step in reversed(backward)],
                 convert(right_hint, z['case']['call']))


def produce(before, after, selected, directory, *, compact=False):
    if before['semantics'] != 'ink-action-transition-v1' or after['semantics'] != before['semantics']:
        raise ValueError('incompatible action projections')
    if not before.get('frozen_domain') or before['frozen_domain'] != after.get('frozen_domain'):
        raise ValueError('requires unchanged checked frozen facts')
    if before['state'] != after['state'] or before['events'] != after['events']:
        raise ValueError('transition representation changed')
    objects = {**before['objects'], **after['objects']}
    bridges = None
    if compact:
        try:
            bridges = ClosedDataBridges(objects)
            objects = bridges.objects
        except ValueError as error:
            if not any(bound in str(error) for bound in ('budget', 'depth limit', 'byte limit')):
                raise
            # Optional candidate discovery must not reject the old tactic.
            # Construction is transactional: its partial objects stay private.
            bridges = None
    proofs = {}
    for name, a in before['actions'].items():
        z = after['actions'][name]
        arguments = [var(n) for n, _ in a['params']]
        old, new = call(a['function'], arguments), call(z['function'], arguments)
        if a['function'] == z['function']:
            proofs[name] = {'Refl': old}
            continue
        bindings = a['case']['bindings']
        state = cons(before['state'], 0, [var(n) for n in bindings])
        if compact:
            case = compact_equality(a, z, state, before['frozen_domain'], objects, bridges)
        else:
            facts = [(sub(eq['from'], {'initial': state}), sub(eq['to'], {'initial': state}), i)
                     for i, eq in enumerate(before['frozen_domain'])]
            case = equality(a['case']['call'], z['case']['call'], objects, facts=facts)
        # Case elimination substitutes the same state constructor in the goal
        # and all premises. It grants no recursive induction hypothesis.
        proofs[name] = {'Cases': dict(variable='initial', **{'from': old, 'to': new},
                                      cases=[dict(bindings=bindings, proof=case)])}
    roots = {a['function'] for m in (before, after) for a in m['actions'].values()}
    if bridges:
        roots.update(bridges.lemmas)
    def fixed_references(value):
        if isinstance(value, dict):
            function = value.get('function')
            if isinstance(function, str) and function in objects:
                roots.add(function)
            for child in value.values():
                fixed_references(child)
        elif isinstance(value, list):
            for child in value:
                fixed_references(child)
    # Large fixed rows use transparent closed definitions. Their meaning must
    # remain in the checked closure even if no surviving action reads the root.
    fixed_references(before['frozen_domain'])
    roots = sorted(roots)
    store = Store.publish(directory, list(objects.values()))
    return dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=before['source'],
                knowledge=store.bundle(roots), applications=[],
                action_replacement=dict(selected=selected, proofs=proofs))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source', type=Path, help='checked frozen executable core JSON')
    p.add_argument('--ink', type=Path, required=True)
    p.add_argument('-o', '--output', type=Path, required=True)
    a = p.parse_args()
    if a.source.stat().st_size > 16000000:
        raise ValueError('source byte limit')
    source = json.loads(a.source.read_bytes())
    selected = specialize(source)
    a.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='ink-frozen-proposal-') as temp:
        temp = Path(temp)
        candidate = temp/'selected.json'
        candidate.write_text(json.dumps(selected))
        def model(path, output):
            subprocess.run([str(a.ink.resolve()), 'emit-action-model', str(path), '--core', '-o', str(output)], check=True, capture_output=True)
            return json.loads(output.read_bytes())
        before = model(a.source, temp/'before.json')
        after = model(candidate, temp/'after.json')
        proposal = temp/'selection.json'
        for strategy in ('compact', 'normalized'):
            packet = produce(before, after, selected, temp/'database', compact=strategy == 'compact')
            proposal.write_text(json.dumps(packet, separators=(',', ':'))+'\n')
            checked = subprocess.run([str(a.ink.resolve()), 'check-selection', str(a.source), str(proposal)], capture_output=True)
            if checked.returncode == 0:
                break
            if strategy == 'normalized':
                checked.check_returncode()
        # A failed producer/check leaves no new selection at the requested path.
        a.output.write_bytes(proposal.read_bytes())
    print(json.dumps(dict(status='checked-proposal', actions=len(packet['action_replacement']['proofs']),
                          proof_strategy=strategy,
                          profitability='unmeasured; explicit selection only')))


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.stderr.decode(errors='replace').strip() or 'compiler rejected specialization')
