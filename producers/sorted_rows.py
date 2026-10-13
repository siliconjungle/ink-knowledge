#!/usr/bin/env python3
"""Untrusted proofs about strictly sorted keyed rows.

The checker can assume that every table of a module is strictly sorted only
after an inductive-invariant check (`ink-sorted-tables-v1`): the original
actions must preserve sortedness, proved here from general row laws. On
sorted rows, removing one key commutes with inserting a different key, which
is false on arbitrary row lists. Laws are stated once over state-calculus's
abstract row sort with word keys and reach programs only through checked
instances; this producer's normaliser and search grant nothing.

The proof search (`Engine`) normalises, rewrites with hypotheses and
conditional laws, and splits on Boolean conditions. Every step it proposes is
an ordinary Convert, Substitute, BoolSplit, Use or Instance node that the
kernel replays.
"""
import json
from producers.point_delta import normal as base_normal, binary, choice, match, free_variables, sub
from producers.action_replacement import alpha_normal
from producers.general_laws import var, call, construct, hyp, sym, trans, self_call

HOLE = 'delta_hole'
TERM_KEYS = {'Var', 'Bool', 'U64', 'Construct', 'Call', 'SelfCall', 'Binary', 'If', 'Match'}


def convert(a, z):
    return {'Convert': {'from': a, 'to': z}}


def lift(equality, context):
    return {'Substitute': dict(variable=HOLE, context=context, equality=equality)}


def is_term(t):
    return isinstance(t, dict) and len(t) == 1 and next(iter(t)) in TERM_KEYS


def fold(t):
    """Mirror the kernel: equality of identical sides folds to a literal."""
    if isinstance(t, list):
        return [fold(x) for x in t]
    if not isinstance(t, dict):
        return t
    t = {k: fold(v) for k, v in t.items()}
    if 'Binary' in t and t['Binary']['op'] in ('==', '!='):
        x = t['Binary']
        if alpha_normal(x['left']) == alpha_normal(x['right']):
            return {'Bool': x['op'] == '=='}
    if 'If' in t and 'Bool' in t['If']['condition']:
        return t['If']['on_true' if t['If']['condition']['Bool'] else 'on_false']
    return t


def norm(t, objects):
    for _ in range(8):
        n = fold(base_normal(t, objects))
        if n == t:
            break
        t = n
    return alpha_normal(t)


def subterms(t, path=()):
    """Terms in post-order (innermost first), with their paths."""
    if not is_term(t):
        return
    kind, body = next(iter(t.items()))
    if kind in ('Construct', 'Call'):
        for i, a in enumerate(body['arguments']):
            yield from subterms(a, path + (kind, 'arguments', i))
    elif kind == 'SelfCall':
        for i, a in enumerate(body):
            yield from subterms(a, path + (kind, i))
    elif kind == 'Binary':
        for side in ('left', 'right'):
            yield from subterms(body[side], path + (kind, side))
    elif kind == 'If':
        for side in ('condition', 'on_true', 'on_false'):
            yield from subterms(body[side], path + (kind, side))
    elif kind == 'Match':
        yield from subterms(body['scrutinee'], path + (kind, 'scrutinee'))
        for i, b in enumerate(body['branches']):
            yield from subterms(b['body'], path + (kind, 'branches', i, 'body'))
    yield path, t


def children(t):
    kind, body = next(iter(t.items()))
    if kind in ('Construct', 'Call'):
        return [((kind, 'arguments', i), a) for i, a in enumerate(body['arguments'])]
    if kind == 'SelfCall':
        return [((kind, i), a) for i, a in enumerate(body)]
    if kind == 'Binary':
        return [((kind, side), body[side]) for side in ('left', 'right')]
    if kind == 'If':
        return [((kind, side), body[side]) for side in ('condition', 'on_true', 'on_false')]
    if kind == 'Match':
        return [((kind, 'scrutinee'), body['scrutinee'])] + [((kind, 'branches', i, 'body'), b['body']) for i, b in enumerate(body['branches'])]
    return []


def replace_all(t, old, new):
    if t == old:
        return new
    if isinstance(t, list):
        return [replace_all(x, old, new) for x in t]
    if isinstance(t, dict):
        return {k: replace_all(x, old, new) for k, x in t.items()}
    return t


def at(t, path, value):
    if not path:
        return value
    if isinstance(t, dict):
        out = dict(t)
        out[path[0]] = at(t[path[0]], path[1:], value)
        return out
    out = list(t)
    out[path[0]] = at(t[path[0]], path[1:], value)
    return out


def unify(p, t, b):
    if isinstance(p, dict) and set(p) == {'Var'} and p['Var'].startswith('?'):
        name = p['Var']
        if name in b:
            return b if b[name] == t else None
        return {**b, name: t}
    if type(p) is not type(t):
        return None
    if isinstance(p, dict):
        if p.keys() != t.keys():
            return None
        for k in p:
            b = unify(p[k], t[k], b)
            if b is None:
                return None
        return b
    if isinstance(p, list):
        if len(p) != len(t):
            return None
        for x, y in zip(p, t):
            b = unify(x, y, b)
            if b is None:
                return None
        return b
    return b if p == t else None


def instantiate(t, b):
    return sub(t, b) if b else t


def metas(names):
    return {n: var('?' + n) for n in names}


class Fact:
    def __init__(self, term, value, proof):
        self.term, self.value, self.proof = term, value, proof


class Rule:
    """Rewrite `lhs -> rhs` when every premise holds.

    `lhs`, `rhs` and premises are written over metavariables `?name`.
    `build(binding, premise_proofs)` proves the instantiated raw lhs = rhs.
    """
    def __init__(self, name, params, lhs, rhs, premises, build, orient=None):
        self.name, self.params, self.lhs, self.rhs = name, params, lhs, rhs
        self.premises, self.build = premises, build
        # For a law whose sides differ only by swapping two arguments, the
        # pair that must be in descending order before it applies; so it
        # rewrites towards one canonical order and never loops.
        self.orient = orient
        self.pattern = None

    def prepare(self, objects):
        if self.pattern is None:
            self.pattern = norm(sub(self.lhs, metas(self.params)), objects)
        return self.pattern


def guarded(guards, inner, default):
    """Nested conditions: `(g, True)` keeps `inner` when g holds,
    `(g, False)` keeps it when g fails; otherwise `default`."""
    for g, polarity in reversed(guards):
        inner = choice(g, inner, default) if polarity else choice(g, default, inner)
    return inner


def discharge(guards, inner, default, guard_proofs):
    """inner = guarded(guards, inner, default), given proofs `g = polarity`."""
    literal = [({'Bool': pol}, pol) for _, pol in guards]
    steps = [convert(inner, guarded(literal, inner, default))]
    for i, (proof, (g, pol)) in enumerate(zip(guard_proofs, guards)):
        context = guarded(guards[:i] + [(var(HOLE), pol)] + literal[i + 1:], inner, default)
        steps.append(lift(sym(proof), context))
    return trans(*steps)


def canonical_term(t):
    return json.dumps(t, sort_keys=True, separators=(',', ':'))


def law_rule(name, params, conditions, guards, left, right, default, cite, orient=None):
    """A conditional law as a rewrite. `cite(binding, condition_proofs)` is
    its Use/Instance/hypothesis node proving the guarded statement."""
    premises = [(c['from'], c['to']) for c in conditions] + [(g, {'Bool': pol}) for g, pol in guards]

    def build(b, proofs):
        n = len(conditions)
        g = [(instantiate(x, b), pol) for x, pol in guards]
        lhs, rhs = instantiate(left, b), instantiate(right, b)
        d = instantiate(default, b)
        statement = cite(b, proofs[:n])
        if not guards:
            return statement
        steps = [discharge(g, lhs, d, proofs[n:]), statement]
        if right != {'Bool': True} or default != {'Bool': True}:
            steps.append(sym(discharge(g, rhs, d, proofs[n:])))
        return trans(*steps)
    return Rule(name, params, left, right, premises, build, orient)


class Engine:
    def __init__(self, objects, env, rules=(), depth=6, words=()):
        self.objects, self.env, self.rules, self.depth = objects, set(env), list(rules), depth
        # Candidate values for a premise variable that no fact determines.
        self.words = [var(w) for w in words]

    def n(self, t):
        return norm(t, self.objects)

    def closed(self, t):
        return free_variables(t) <= self.env

    def premise(self, pattern, expected, b, facts, depth):
        """Prove an instantiated premise; unbound metavariables bind to facts."""
        expected_n = self.n(expected)
        pattern = instantiate(pattern, b)
        unbound = sorted(x for x in free_variables(pattern) if x.startswith('?'))
        if unbound:
            normalised = norm(pattern, self.objects)
            for f in facts:
                if f.value != expected_n:
                    continue
                found = unify(normalised, f.term, b)
                if found is not None:
                    return found, f.proof
            if len(unbound) == 1 and depth <= 2:
                for w in self.words:
                    found, proof = self.premise(pattern, expected, {**b, unbound[0]: w}, facts, depth)
                    if found is not None:
                        return found, proof
            return None, None
        term = pattern
        if depth > 2:
            # Shallow lookups only: premises are facts or one rewrite away.
            key = self.n(term)
            hit = next((f for f in facts if f.term == key and f.value == expected_n), None)
            return (b, hit.proof) if hit else (None, None)
        value, steps = self.simp(term, facts, depth + 1)
        if value != expected_n:
            return None, None
        return b, (trans(*steps) if steps else {'Refl': term})

    def apply(self, rule, s, facts, depth):
        pattern = rule.prepare(self.objects)
        b = unify(pattern, alpha_normal(s), {})
        if b is None:
            return None
        if rule.orient and all('?' + n in b for n in rule.orient) and \
                canonical_term(b['?' + rule.orient[0]]) <= canonical_term(b['?' + rule.orient[1]]):
            return None
        proofs = []
        for p, expected in rule.premises:
            p = sub(p, metas(rule.params))
            b2, proof = self.premise(p, expected, b, facts, depth)
            if b2 is None:
                return None
            b = b2
            proofs.append(proof)
        binding = {k[1:]: v for k, v in b.items()}
        if set(binding) != set(rule.params):
            return None
        if rule.orient and canonical_term(binding[rule.orient[0]]) <= canonical_term(binding[rule.orient[1]]):
            return None
        return rule.build(binding, proofs), instantiate(rule.rhs, binding)

    def simp(self, t, facts, depth=0):
        """Normal form under hypotheses and laws, with one Substitute per
        rewrite. Steps chain by normalisation: the kernel compares adjacent
        terms up to computation, so no conversions between them are needed."""
        current = self.n(t)
        steps = []
        for _ in range(64):
            for path, s in subterms(current):
                if not self.closed(s) or set(s) & {'Bool', 'U64'}:
                    continue
                key = alpha_normal(s)
                step = None
                for f in facts:
                    if f.term == key:
                        step = (f.proof, f.value)
                        break
                if step is None and depth < 4:
                    for rule in self.rules:
                        applied = self.apply(rule, s, facts, depth)
                        if applied:
                            step = applied
                            break
                if step:
                    equality, after = step
                    # Every identical occurrence in one Substitute.
                    context = replace_all(current, s, var(HOLE))
                    steps.append(lift(equality, context))
                    current = self.n(replace_all(current, s, after))
                    break
            else:
                return current, steps
        raise ValueError('rewrite budget exhausted')

    def split(self, terms):
        """The outermost open condition: guards first, so inner conditions
        are usually decided by laws rather than split."""
        def walk(t):
            if not is_term(t):
                return None
            if 'If' in t:
                # Split on atomic conditions: one containing another
                # conditional is decided by splitting that one first.
                c = t['If']['condition']
                inner = walk(c)
                if inner is not None:
                    return inner
                if self.closed(c) and 'Bool' not in c:
                    return c
            for _, child in children(t):
                found = walk(child)
                if found is not None:
                    return found
            return None
        for t in terms:
            found = walk(t)
            if found is not None:
                return found
        return None

    def contradiction(self, facts):
        """A proof of `true = false` when laws refute some hypothesis."""
        for i, f in enumerate(facts):
            if 'Bool' not in f.value:
                continue
            others = facts[:i] + facts[i + 1:]
            value, steps = self.simp(f.term, others, 1)
            if 'Bool' in value and value != f.value and steps:
                proof = trans(*steps)
                # proof: term = value; f.proof: term = f.value.
                first, second = (f.proof, proof) if f.value['Bool'] else (proof, f.proof)
                return trans(sym(first), second)
        return None

    def prove(self, a, z, facts, hypotheses, depth=0):
        na, pa = self.simp(a, facts)
        nz, pz = self.simp(z, facts)
        if na == nz:
            if not pa and not pz:
                return {'Refl': a}
            return trans(*pa, *([sym(trans(*pz))] if pz else []))
        absurd = self.contradiction(facts)
        if absurd is not None:
            # Ex falso: a = if true {a} else {z} = if false {a} else {z} = z.
            return trans(convert(a, choice({'Bool': True}, a, z)), lift(absurd, choice(var(HOLE), a, z)),
                         convert(choice({'Bool': False}, a, z), z))
        if depth >= self.depth:
            raise ValueError(f'cannot establish: {json.dumps(na)[:600]} = {json.dumps(nz)[:600]}')
        condition = self.split([na, nz])
        if condition is None:
            raise ValueError(f'no split: {json.dumps(na)[:600]} = {json.dumps(nz)[:600]}')
        branches = {}
        for flag in (False, True):
            fact = Fact(self.n(condition), {'Bool': flag}, hyp(hypotheses))
            branches['on_true' if flag else 'on_false'] = self.prove(a, z, facts + [fact], hypotheses + 1, depth + 1)
        return {'BoolSplit': dict(condition=condition, **{'from': a, 'to': z}, **branches)}


def facts_from(conditions, objects):
    return [Fact(norm(c['from'], objects), norm(c['to'], objects), hyp(i)) for i, c in enumerate(conditions)]


# ---------------------------------------------------------------------------
# General laws over state-calculus rows (word keys, abstract row values).

class Law:
    """`guarded(guards, left, default) = guarded(guards, right, default)`,
    or `... = true` when `right` and `default` are both `true`."""
    def __init__(self, name, params, conditions, guards, left, right, default):
        self.name, self.params, self.conditions = name, params, conditions
        self.guards, self.left, self.right, self.default = guards, left, right, default

    @property
    def boolean(self):
        return self.right == {'Bool': True} and self.default == {'Bool': True}

    def statement(self):
        lhs = guarded(self.guards, self.left, self.default)
        rhs = {'Bool': True} if self.boolean else guarded(self.guards, self.right, self.default)
        return lhs, rhs

    def rule(self, cite):
        return law_rule(self.name, [n for n, _ in self.params], self.conditions, self.guards,
                        self.left, self.right, self.default, cite, COMMUTATIONS.get(self.name))


# Laws whose two sides differ only by the order of two writes: apply only
# when (first, second) are in descending canonical order.
COMMUTATIONS = {'insert_insert_commute': ('key', 'other'), 'replace_replace_commute': ('key', 'other'),
                'remove_remove_commute': ('key', 'other')}


def instance_for(law, substitute):
    """The same law with its statement terms rewritten (row variable -> tail)."""
    return Law(law.name, law.params, law.conditions,
               [(substitute(g), pol) for g, pol in law.guards],
               substitute(law.left), substitute(law.right), substitute(law.default))


def word_certificate(compiler, goal, cache):
    import subprocess, tempfile
    from pathlib import Path
    from producers.bitvector_proofs import certificate
    key = json.dumps(goal, sort_keys=True)
    if key in cache:
        return cache[key]
    with tempfile.TemporaryDirectory(prefix='ink-sorted-rows-') as temp:
        source = Path(temp) / 'goal.json'
        cnf = Path(temp) / 'cnf.json'
        source.write_text(json.dumps(goal))
        subprocess.run([str(compiler), 'bitvector-obligation', str(source), '-o', str(cnf)], check=True, capture_output=True)
        cache[key] = certificate(json.loads(cnf.read_text()))
    return cache[key]


T, F = {'Bool': True}, {'Bool': False}


def lt(a, z):
    return binary('<', a, z)


def eq(a, z):
    return binary('==', a, z)


def is_(term, value):
    return {'from': term, 'to': value}


def definitions(lib):
    """The projection's own row definitions (core/src/action_model): insertion
    by word order, and strictly ascending keys above an exclusive bound."""
    N = lib.names
    M = lambda scrutinee, *branches: match(scrutinee, list(branches))
    rows_id, row = N['WordRows'], {'Data': N['StateRow']}
    RS = {'Data': rows_id}
    r, k, n, b = map(var, ('rows', 'key', 'new', 'bound'))
    h, x, t = map(var, ('head', 'value', 'tail'))
    nil = construct(rows_id, 0)
    cons = lambda key, value, tail: construct(rows_id, 1, key, value, tail)
    lib.function('insert', [['rows', RS], ['key', 'U64'], ['new', row]], RS,
                 M(r, ([], cons(k, n, nil)),
                   (['head', 'value', 'tail'], choice(lt(k, h), cons(k, n, r), cons(h, x, self_call(t, k, n))))), 0)
    sk, st = var('sorted_key'), var('sorted_tail')
    above = lib.function('above', [['rows', RS], ['bound', 'U64']], 'Bool',
                         M(r, ([], T), (['sorted_key', 'sorted_value', 'sorted_tail'],
                                        choice(lt(b, sk), self_call(st, sk), F))), 0)
    lib.function('sorted', [['rows', RS]], 'Bool',
                 M(r, ([], T), (['sorted_key', 'sorted_value', 'sorted_tail'], call(above, st, sk))))


# Word facts, checked by bit-blasting: (name, params, conditions, left, right).
def word_statements():
    a, b_, c, d = map(var, ('a', 'b', 'c', 'd'))
    return [
        ('word_less_transitive', ['a', 'b', 'c'], [is_(lt(a, b_), T), is_(lt(b_, c), T)], lt(a, c), T),
        ('word_less_total', ['a', 'b'], [is_(lt(b_, a), F), is_(eq(b_, a), F)], lt(a, b_), T),
        ('word_at_most_unequal', ['b', 'c', 'd'], [is_(lt(c, b_), F), is_(lt(c, d), T)], eq(b_, d), F),
        ('word_at_most_not_above', ['b', 'c', 'd'], [is_(lt(c, b_), F), is_(lt(c, d), T)], lt(d, b_), F),
        ('word_equal_not_less', ['a', 'b'], [is_(eq(a, b_), T)], lt(b_, a), F),
        ('word_unequal_symmetric', ['a', 'b'], [is_(eq(a, b_), F)], eq(b_, a), F),
        ('word_differ_unequal', ['a', 'b'], [is_(binary('!=', a, b_), T)], eq(a, b_), F),
        ('word_differ_unequal_symmetric', ['a', 'b'], [is_(binary('!=', a, b_), T)], eq(b_, a), F),
        ('word_less_asymmetric', ['a', 'b'], [is_(lt(a, b_), T)], lt(b_, a), F),
        ('word_equal_transitive', ['a', 'b', 'c'], [is_(eq(a, c), T), is_(eq(b_, c), T)], eq(a, b_), T),
    ]


def statements(N):
    """Row laws in proof order, with how each is proved. `N` maps role names
    (WordRows, StateRow, get, remove, replace, contains, insert, above,
    sorted) to definition identities, general or program-specific."""
    rows_id, row = N['WordRows'], {'Data': N['StateRow']}
    RS = {'Data': rows_id}
    r, k, n, b, o, m = map(var, ('rows', 'key', 'new', 'bound', 'other', 'mid'))
    cons = lambda key, value, tail: construct(rows_id, 1, key, value, tail)
    I = lambda rows, key, new: call(N['insert'], rows, key, new)
    D = lambda rows, key: call(N['remove'], rows, key)
    R = lambda rows, key, new: call(N['replace'], rows, key, new)
    A = lambda rows, bound: call(N['above'], rows, bound)
    S = lambda rows: call(N['sorted'], rows)
    C = lambda rows, key: call(N['contains'], rows, key)
    G = lambda rows, key: call(N['get'], rows, key)
    P = lambda *names: [(nm, {'rows': RS, 'new': row, 'payload': row}.get(nm, 'U64')) for nm in names]
    pl = var('payload')
    cases, induction = ('cases', 'rows'), lambda *g: ('induction', 'rows', list(g))
    apart = [is_(eq(o, k), F)]
    out = [
        (Law('above_weaken', P('rows', 'bound', 'mid'), [], [(lt(b, m), True), (A(r, m), True)], A(r, b), T, T), cases),
        (Law('above_remove', P('rows', 'bound', 'key'), [], [(A(r, b), True)], A(D(r, k), b), T, T), induction('bound')),
        (Law('above_replace', P('rows', 'bound', 'key', 'new'), [], [(A(r, b), True)], A(R(r, k, n), b), T, T), induction('bound')),
        (Law('above_insert', P('rows', 'bound', 'key', 'new'), [], [(A(r, b), True), (lt(b, k), True), (C(r, k), False)],
             A(I(r, k, n), b), T, T), induction('bound')),
        (Law('above_sorted', P('rows', 'bound'), [], [(A(r, b), True)], S(r), T, T), cases),
        (Law('sorted_remove', P('rows', 'key'), [], [(S(r), True)], S(D(r, k)), T, T), cases),
        (Law('sorted_replace', P('rows', 'key', 'new'), [], [(S(r), True)], S(R(r, k, n)), T, T), cases),
        (Law('sorted_insert', P('rows', 'key', 'new'), [], [(S(r), True), (C(r, k), False)], S(I(r, k, n)), T, T), cases),
        (Law('above_absent_remove', P('rows', 'bound', 'key'), [], [(A(r, b), True), (lt(b, k), False)], D(r, k), r, r),
         induction('bound')),
        (Law('above_front_insert', P('rows', 'bound', 'key', 'new'), [], [(A(r, b), True), (lt(k, b), True)],
             I(r, k, n), cons(k, n, r), cons(k, n, r)), cases),
        (Law('above_remove_insert_commute', P('rows', 'bound', 'key', 'new', 'other'), apart, [(A(r, b), True)],
             D(I(r, k, n), o), I(D(r, o), k, n), r), induction('bound')),
        (Law('sorted_remove_insert_commute', P('rows', 'key', 'new', 'other'), apart, [(S(r), True)],
             D(I(r, k, n), o), I(D(r, o), k, n), r), cases),
        (Law('lookup_insert_other', P('rows', 'key', 'new', 'other'), apart, [], G(I(r, k, n), o), G(r, o), G(r, o)),
         induction()),
        # Writes of two different keys commute on any row list.
        (Law('insert_insert_commute', P('rows', 'key', 'new', 'other', 'payload'), apart, [],
             I(I(r, k, n), o, pl), I(I(r, o, pl), k, n), r), induction()),
        (Law('replace_insert_commute', P('rows', 'key', 'new', 'other', 'payload'), apart, [],
             R(I(r, k, n), o, pl), I(R(r, o, pl), k, n), r), induction()),
        (Law('replace_replace_commute', P('rows', 'key', 'new', 'other', 'payload'), apart, [],
             R(R(r, k, n), o, pl), R(R(r, o, pl), k, n), r), induction()),
    ]
    return out


def word_laws():
    return [Law(name, [(p, 'U64') for p in params], conditions, [], left, right, right)
            for name, params, conditions, left, right in word_statements()]


def cite_use(theorem, law):
    return lambda bind, proofs: {'Use': dict(theorem=theorem, arguments=[bind[p] for p, _ in law.params], premises=proofs)}


def build(lib, compiler, certificates):
    """Add sorted-row definitions and checked laws to a state-calculus library."""
    definitions(lib)
    N = lib.names
    rows_id = N['WordRows']
    h, x, t = map(var, ('head', 'value', 'tail'))
    nil, cons = construct(rows_id, 0), construct(rows_id, 1, h, x, t)
    rules, laws = [], {}
    for law in word_laws():
        goal = dict(params=[[p, s] for p, s in law.params], conditions=law.conditions, **{'from': law.left, 'to': law.right})
        cert = word_certificate(compiler, goal, certificates)
        theorem = lib.store(law.name, 'Theorem', dict(**goal, proof={'BitVector': dict(
            **{'from': law.left, 'to': law.right}, hypotheses=list(range(len(law.conditions))), certificate=cert)}))
        laws[law.name] = (law, theorem)
        rules.append(law.rule(cite_use(theorem, law)))

    def engine(env, extra=(), words=()):
        return Engine(lib.objects, env, list(extra) + rules, words=words)

    def by_cases(law, lhs, rhs):
        env = [p for p, _ in law.params]
        cases = []
        for names, value in (([], nil), (['head', 'value', 'tail'], cons)):
            local = [v for v in env if v != 'rows'] + names
            words = [v for v, s in law.params if s == 'U64'] + names[:1]
            a, z = sub(lhs, {'rows': value}), sub(rhs, {'rows': value})
            proof = engine(local, words=words).prove(a, z, facts_from(law.conditions, lib.objects), len(law.conditions))
            cases.append(dict(bindings=names, proof=proof))
        return {'Cases': dict(variable='rows', **{'from': lhs, 'to': rhs}, cases=cases)}

    def by_induction(law, lhs, rhs, generalize):
        """Structural induction; generalized parameters are quantified in the
        induction hypothesis, which becomes a rewrite rule."""
        env = [p for p, _ in law.params]
        cases = []
        for names, value in (([], nil), (['head', 'value', 'tail'], cons)):
            local = [v for v in env if v != 'rows'] + names
            words = [v for v, s in law.params if s == 'U64'] + names[:1]
            a, z = sub(lhs, {'rows': value}), sub(rhs, {'rows': value})
            extra, hypotheses = [], len(law.conditions)
            if names:
                tail = instance_for(law, lambda term: sub(term, {'rows': t}))
                if generalize:
                    ih = Law('induction', [(p, s) for p, s in law.params if p in generalize], [],
                             tail.guards, tail.left, tail.right, tail.default)
                    extra.append(ih.rule(lambda bind, proofs: {'GeneralizedHypothesis': dict(
                        index=0, arguments=[bind[p] for p in generalize])}))
                else:
                    ih = Law('induction', [], [], tail.guards, tail.left, tail.right, tail.default)
                    extra.append(ih.rule(lambda bind, proofs, i=hypotheses: hyp(i)))
                    hypotheses += 1
            proof = engine(local, extra, words).prove(a, z, facts_from(law.conditions, lib.objects), hypotheses)
            cases.append(dict(bindings=names, proof=proof))
        body = dict(variable='rows', **{'from': lhs, 'to': rhs}, cases=cases)
        if generalize:
            return {'GeneralizedInduction': dict(variable='rows', generalize=generalize, **{'from': lhs, 'to': rhs}, cases=cases)}
        return {'Induction': body}

    for law, how in statements(N):
        lhs, rhs = law.statement()
        proof = by_cases(law, lhs, rhs) if how[0] == 'cases' else by_induction(law, lhs, rhs, how[2])
        theorem = lib.store(law.name, 'Theorem', dict(params=[[p, s] for p, s in law.params], conditions=law.conditions,
                                                     **{'from': lhs, 'to': rhs}, proof=proof))
        laws[law.name] = (law, theorem)
        rules.append(law.rule(cite_use(theorem, law)))
    return laws


# ---------------------------------------------------------------------------
# Programs: invariant preservation and transition equality under sorted tables.

ROLES = ('WordRows', 'StateRow', 'RowOption', 'get', 'remove', 'replace', 'contains', 'insert', 'above', 'sorted')
# Published state-calculus laws reused here. `lookup_general_replace` is not:
# its statement reaches a helper (`replace_present`) programs do not define.
EQUATIONS = ('lookup_general_remove', 'remove_replace_commute', 'remove_remove_commute',
             'lookup_remove_other_key', 'lookup_replace_other_key')


def published_law(name, d, mapping):
    """A stored equation as a rule; `if c {d} else {x} = if c {d} else {y}`
    becomes the guarded rewrite x -> y when c is false."""
    params = [tuple(p) for p in d['params']]
    conditions = rename_ids(d['conditions'], mapping)
    left, right = rename_ids(d['from'], mapping), rename_ids(d['to'], mapping)
    if 'If' in left and 'If' in right and left['If']['condition'] == right['If']['condition'] \
            and left['If']['on_true'] == right['If']['on_true']:
        return Law(name, params, conditions, [(left['If']['condition'], False)],
                   left['If']['on_false'], right['If']['on_false'], left['If']['on_true'])
    return Law(name, params, conditions, [], left, right, right)


def rename_ids(t, mapping):
    if isinstance(t, list):
        return [rename_ids(x, mapping) for x in t]
    if isinstance(t, dict):
        return {k: (mapping.get(v, v) if k in ('function', 'datatype', 'Data') and isinstance(v, str)
                    else rename_ids(v, mapping)) for k, v in t.items()}
    return t


def declaration(objects, i):
    return objects[i]['payload']['declaration']


def table_roles(model, table, predicate, objects):
    """Program definitions playing each general role, or None when the table's
    keys are not words ordered by `<` (the general laws' key domain)."""
    get = declaration(objects, table['get'])['Function']
    option = get['result']['Data']
    sorted_body = declaration(objects, predicate)['Function']['body']
    above = sorted_body['Match']['branches'][1]['body']['Call']['function']
    insert = declaration(objects, table['insert'])['Function']
    condition = insert['body']['Match']['branches'][1]['body']['If']['condition']
    if condition != lt(var('key'), var('head')) or insert['params'][1][1] != 'U64':
        return None
    value = model['types'][json.dumps(table['value_type'], sort_keys=True, separators=(',', ':'))]
    return dict(WordRows=table['datatype'], StateRow=value, RowOption=option, get=table['get'], remove=table['remove'],
                replace=table['replace'], contains=table['contains'], insert=table['insert'], above=above, sorted=predicate)


def program_rules(model, sorted_tables, objects, names):
    """Rewrite rules for one module: word facts, and instances of the general
    row laws for every table whose keys are words."""
    general = {role: names['state-calculus/' + role] for role in ROLES}
    used, rules = set(), []
    for law in word_laws():
        theorem = names['state-calculus/' + law.name]

        def cite(bind, proofs, theorem=theorem, law=law):
            used.add(theorem)
            return cite_use(theorem, law)(bind, proofs)
        rules.append(law.rule(cite))
    for table, predicate in zip(model['tables'], sorted_tables['predicates']):
        roles = table_roles(model, table, predicate, objects)
        if roles is None:
            continue
        definitions = {general[r]: roles[r] for r in ROLES if r != 'StateRow'}
        sorts = {general['StateRow']: roles['StateRow']}
        mapping = {general[r]: roles[r] for r in ROLES}
        laws = [law for law, _ in statements(roles)]
        for name in EQUATIONS:
            laws.append(published_law(name, declaration(objects, names['state-calculus/' + name])['Theorem'], mapping))
        for law in laws:
            theorem = names['state-calculus/' + law.name]

            def cite(bind, proofs, theorem=theorem, law=law, definitions=definitions):
                # The instance names program definitions; publish them all.
                used.add(theorem)
                used.update(definitions.values())
                return {'Instance': dict(theorem=theorem, sorts=sorts, functions={}, definitions=definitions,
                                         assumptions={}, arguments=[bind[p] for p, _ in law.params], premises=proofs)}
            rules.append(law.rule(cite))
    return rules, used


def root(tables, index, state):
    names = [f'sorted_root_{i}' for i in range(tables)]
    return match(state, [(names, var(names[index]))])


def hypotheses(model, sorted_tables, state):
    n = len(model['tables'])
    return [is_(call(p, root(n, i, state)), T) for i, p in enumerate(sorted_tables['predicates'])]


def obligation(model, sorted_tables, action, table):
    """Exactly core's preservation goal (Projection::sorted_obligation)."""
    a = model['actions'][action]
    n = len(model['tables'])
    holds = lambda s: call(sorted_tables['predicates'][table], root(n, table, var(s)))
    reply = [f'sorted_after_{x}' for x in ('reply', 'commit', 'version', 'state', 'events')]
    host = [f'sorted_host_{x}' for x in ('code', 'version', 'state')]
    applied = call(a['function'], *[var(p) for p, _ in a['params']])
    return match(applied, [(reply, holds('sorted_after_state')), (host, holds('sorted_host_state'))])


def by_state_cases(model, sorted_tables, action, lhs, rhs, objects, rules, depth=10):
    """Case on the logical state, so each table is a variable whose sortedness
    is a hypothesis, then search."""
    a = model['actions'][action]
    n = len(model['tables'])
    bindings = [f'sorted_rows_{i}' for i in range(n)]
    state = construct(model['state'], 0, *map(var, bindings))
    env = [p for p, _ in a['params'] if p != 'initial'] + bindings
    words = [p for p, s in a['params'] if s == 'U64']
    facts = facts_from(hypotheses(model, sorted_tables, state), objects)
    engine = Engine(objects, env, rules, depth=depth, words=words)
    proof = engine.prove(sub(lhs, {'initial': state}), sub(rhs, {'initial': state}), facts, n)
    return {'Cases': dict(variable='initial', **{'from': lhs, 'to': rhs}, cases=[dict(bindings=bindings, proof=proof)])}


def action_proofs(before, after, sorted_tables, objects, names):
    """Sorted-table preservation proofs for every original action, and
    whole-transition equality proofs (under the invariant) for changed ones."""
    rules, used = program_rules(before, sorted_tables, objects, names)
    preservation = {}
    for name in before['actions']:
        preservation[name] = [by_state_cases(before, sorted_tables, name, obligation(before, sorted_tables, name, i), T, objects, rules)
                              for i in range(len(before['tables']))]
    equalities = {}
    for name, a in before['actions'].items():
        z = after['actions'][name]
        if a['function'] == z['function']:
            continue
        args = [var(p) for p, _ in a['params']]
        equalities[name] = by_state_cases(before, sorted_tables, name, call(a['function'], *args), call(z['function'], *args), objects, rules)
    return preservation, equalities, used
