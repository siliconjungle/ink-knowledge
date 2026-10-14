"""Reusable unsigned-word candidates inspired by compiler value/bit analysis.

These templates have no authority. Offline authoring generates source-bound RUP
certificates, then ordinary knowledge-check admits them. Compilation only loads
the resulting immutable laws; it never invokes LLVM or a SAT solver.
"""
import gzip
import json
from importlib.resources import files
from .semantic_laws import value, var, word, op, term


def templates():
    rows = []
    boolean = value('Bool')
    truth = term(boolean, {'Bool': True})
    for kind in ('U32', 'U64'):
        s = value(kind)
        x, y, z, m, n = [var(s, name) for name in ('x', 'y', 'z', 'm', 'n')]
        zero = word(kind, 0)
        width = 32 if kind == 'U32' else 64
        full = word(kind, (1 << width) - 1)
        AND = lambda a, b: op(s, 'call:word_and', a, b)
        OR = lambda a, b: op(s, 'call:word_or', a, b)
        XOR = lambda a, b: op(s, 'call:word_xor', a, b)
        NOT = lambda a: op(s, 'call:word_not', a)
        ADD = lambda a, b: op(s, 'binary:+', a, b)
        SUB = lambda a, b: op(s, 'binary:-', a, b)
        REL = lambda name, a, b: op(boolean, 'binary:' + name, a, b)
        def add(name, left, right, conditions=()):
            params = {}
            def visit(t):
                node = t['node']
                if 'Free' in node:
                    params[node['Free']] = t['sort']
                for child in node.get('Op', [None, []])[1]:
                    visit(child)
            visit(left); visit(right)
            for condition in conditions:
                visit(condition['from']); visit(condition['to'])
            rows.append(dict(name=kind.lower() + '/' + name,
                             goal=dict(params=params, conditions=list(conditions),
                                       **{'from': left, 'to': right})))
        eq = lambda a, b: {'from': a, 'to': b}
        add('and_idempotent', AND(x, x), x)
        add('or_idempotent', OR(x, x), x)
        add('xor_self', XOR(x, x), zero)
        add('xor_cancel', XOR(XOR(x, y), y), x)
        add('and_absorption', AND(x, OR(x, y)), x)
        add('or_absorption', OR(x, AND(x, y)), x)
        add('and_complement', AND(x, NOT(x)), zero)
        add('or_complement', OR(x, NOT(x)), full)
        add('double_complement', NOT(NOT(x)), x)
        add('mask_intersection', AND(AND(x, m), n), AND(x, AND(m, n)))
        add('mask_union', OR(AND(x, m), AND(x, n)), AND(x, OR(m, n)))
        add('mask_xor', XOR(AND(x, m), AND(x, n)), AND(x, XOR(m, n)))
        add('complementary_partition', OR(AND(x, m), AND(x, NOT(m))), x)
        add('masked_merge', XOR(y, AND(XOR(x, y), m)),
            OR(AND(x, m), AND(y, NOT(m))))
        add('sum_from_union_intersection', ADD(OR(x, y), AND(x, y)), ADD(x, y))
        add('sum_minus_intersection', SUB(ADD(x, y), AND(x, y)), OR(x, y))
        add('disjoint_add', ADD(x, y), OR(x, y), [eq(AND(x, y), zero)])
        add('disjoint_xor', XOR(x, y), OR(x, y), [eq(AND(x, y), zero)])
        add('subset_mask', AND(AND(x, m), n), AND(x, m), [eq(AND(m, n), m)])
        add('mask_upper_bound', REL('<=', AND(x, m), m), truth)
        add('or_lower_bound', REL('>=', OR(x, m), m), truth)
        add('disjoint_mask_zero', AND(x, m), zero, [eq(AND(x, m), zero)])
        # General bound: addition is monotone only when the source proves room.
        add('increment_with_room', REL('>', ADD(x, word(kind, 1)), x), truth,
            [eq(REL('<', x, full), truth)])
        # Truncating to the low bits commutes with wrapping addition. A variable
        # mask is supported under an explicit low-mask premise, including 0/MAX.
        add('low_mask_add', AND(ADD(AND(x, m), AND(y, m)), m), AND(ADD(x, y), m),
            [eq(AND(m, ADD(m, word(kind, 1))), zero)])
        # Arithmetic fusion that remains correct at the word boundary.
        add('cancel_add_left', SUB(ADD(x, y), x), y)
        add('cancel_sub_left', ADD(SUB(x, y), y), x)
    return rows


def specialize(subject, core):
    from ink_planner.semantic_search import positions, match
    resource = files('producers').joinpath('data/word-identities.json.gz')
    rows = json.loads(gzip.decompress(resource.read_bytes()))
    sites = [t for body in subject.get('functions', {}).values() for _, t in positions(body)]
    return [('word-identity/' + row['name'], row['law']) for row in rows
            if any(match(row['law']['from'], t, row['law']['params'], {}) for t in sites)]
