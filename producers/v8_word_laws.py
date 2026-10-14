"""Offline word/branch proposals derived from V8's machine reducers.

Only frozen, independently replayable equality proofs reach compilation. This
module neither invokes V8 nor imports its speculative types, flags or feedback.
All arithmetic is Ink wrapping arithmetic and shift counts use Ink's modulus.
"""
from importlib.resources import files
from .semantic_laws import value, var, word, op, term

UPSTREAM_REVISION = 'c4e049d3cbda775e2c3af9410f6e18b18388d68b'


def templates():
    rows = []
    boolean = value('Bool')
    truth = term(boolean, {'Bool': True})
    for kind, width in (('U32', 32), ('U64', 64)):
        sort = value(kind)
        x, y, z, m, n = [var(sort, name) for name in ('x', 'y', 'z', 'm', 'n')]
        c = var(boolean, 'c')
        k, j = [var(value('U32'), name) for name in ('k', 'j')]
        zero, full = word(kind, 0), word(kind, (1 << width) - 1)
        AND = lambda a, b: op(sort, 'call:word_and', a, b)
        OR = lambda a, b: op(sort, 'call:word_or', a, b)
        XOR = lambda a, b: op(sort, 'call:word_xor', a, b)
        NOT = lambda a: op(sort, 'call:word_not', a)
        ADD = lambda a, b: op(sort, 'binary:+', a, b)
        SUB = lambda a, b: op(sort, 'binary:-', a, b)
        SHL = lambda a, b: op(sort, 'call:wrapping_shl', a, b)
        SHR = lambda a, b: op(sort, 'call:wrapping_shr', a, b)
        EQ = lambda a, b: op(boolean, 'binary:==', a, b)
        CHOOSE = lambda a, b, e: op(sort, 'call:choose', a, b, e)
        BOTH = lambda a, b: op(boolean, 'binary:&&', a, b)
        eq = lambda a, b: {'from': a, 'to': b}
        def add(name, left, right, conditions=()):
            params = {}
            def visit(t):
                node = t['node']
                if 'Free' in node:
                    params[node['Free']] = t['sort']
                for child in node.get('Op', [None, []])[1]:
                    visit(child)
            for t in [left, right] + [t for e in conditions for t in (e['from'], e['to'])]:
                visit(t)
            rows.append(dict(name=kind.lower() + '/' + name,
                             goal=dict(params=params, conditions=list(conditions),
                                       **{'from': left, 'to': right})))
        # Fixed-width masks, cancellation and comparison contraction. Conditions
        # are explicit equalities, never speculative shape/range annotations.
        add('or_covers_mask', OR(AND(x, m), n), OR(x, n), [eq(OR(m, n), full)])
        add('and_covers_union', AND(OR(x, m), n), AND(x, n), [eq(AND(m, n), zero)])
        add('xor_complements', XOR(x, full), NOT(x))
        add('equal_xor_zero', EQ(XOR(x, y), zero), EQ(x, y))
        add('equal_sub_zero', EQ(SUB(x, y), zero), EQ(x, y))
        add('equal_same_add', EQ(ADD(x, z), ADD(y, z)), EQ(x, y))
        add('equal_same_xor', EQ(XOR(x, z), XOR(y, z)), EQ(x, y))
        add('equal_same_sub', EQ(SUB(x, z), SUB(y, z)), EQ(x, y))
        add('bitfield_checks', BOTH(EQ(AND(x, m), y), EQ(AND(x, n), z)),
            EQ(AND(x, OR(m, n)), OR(y, z)),
            [eq(AND(y, NOT(m)), zero), eq(AND(z, NOT(n)), zero),
             eq(AND(y, n), AND(z, m))])
        # Counts remain u32 even when shifting u64. The effective counts are
        # bounded before adding, so no nowrap premise is smuggled into Ink.
        effective = lambda a: op(value('U32'), 'call:word_and', a, word('U32', width - 1))
        a, b = effective(k), effective(j)
        total = op(value('U32'), 'binary:+', a, b)
        fits = op(boolean, 'binary:<', total, word('U32', width))
        for label, shift in (('left', SHL), ('right', SHR)):
            add('shift_' + label + '_count_mask', shift(x, op(value('U32'), 'call:word_and', k, var(value('U32'), 'mask'))),
                shift(x, k), [eq(op(value('U32'), 'call:word_and', var(value('U32'), 'mask'), word('U32', width - 1)), word('U32', width - 1))])
            add('shift_' + label + '_combine', shift(shift(x, k), j), shift(x, total), [eq(fits, truth)])
            add('shift_' + label + '_overflow', shift(shift(x, k), j), zero,
                [eq(fits, term(boolean, {'Bool': False}))])
            for bit_label, bitwise in (('and', AND), ('or', OR), ('xor', XOR)):
                add('shift_' + label + '_' + bit_label, bitwise(shift(x, k), shift(y, k)), shift(bitwise(x, y), k))
        add('right_left_mask', SHL(SHR(x, k), k), AND(x, SHL(full, k)))
        add('left_right_mask', SHR(SHL(x, k), k), AND(x, SHR(full, k)))
        # Path-local control facts are encoded in the *whole* source equality.
        # They cannot survive a merge, nor become assumptions outside a branch.
        add('nested_true_branch', CHOOSE(c, CHOOSE(c, x, y), z), CHOOSE(c, x, z))
        add('nested_false_branch', CHOOSE(c, x, CHOOSE(c, y, z)), CHOOSE(c, x, z))
        add('negated_branch', CHOOSE(EQ(c, term(boolean, {'Bool': False})), x, y), CHOOSE(c, y, x))
        add('identical_branches', CHOOSE(c, x, x), x)
        add('branch_condition_value', EQ(CHOOSE(c, x, y), z),
            op(boolean, 'call:choose', c, EQ(x, z), EQ(y, z)))
        add('select_add', ADD(CHOOSE(c, x, y), CHOOSE(c, z, m)), CHOOSE(c, ADD(x, z), ADD(y, m)))
        add('select_and', AND(CHOOSE(c, x, y), CHOOSE(c, z, m)), CHOOSE(c, AND(x, z), AND(y, m)))
    # Representation round trips and low-word homomorphisms. These use
    # existing total conversions, not V8's tagged-value or overflow assumptions.
    u32, u64 = value('U32'), value('U64')
    x, y, small = var(u64, 'x'), var(u64, 'y'), var(u32, 'small')
    narrow = lambda t: op(u32, 'call:word_narrow_u64_to_u32', t)
    widen = lambda t: op(u64, 'call:word_widen_u32_to_u64', t)
    conversions = [('narrow_widen', narrow(widen(small)), small, {'small':u32}),
                   ('widen_narrow_mask', widen(narrow(x)),
                    op(u64, 'call:word_and', x, word('U64', (1 << 32)-1)), {'x':u64})]
    for label, name in [('and','call:word_and'), ('or','call:word_or'),
                        ('xor','call:word_xor'), ('add','binary:+'),
                        ('sub','binary:-'), ('mul','binary:*')]:
        conversions.append(('narrow_'+label, narrow(op(u64,name,x,y)),
                            op(u32,name,narrow(x),narrow(y)), {'x':u64,'y':u64}))
    for name, left, right, params in conversions:
        rows.append(dict(name='conversion/'+name,
                         goal=dict(params=params,conditions=[],**{'from':left,'to':right})))
    return rows


def specialize(subject, core):
    from .frozen_laws import specialize as indexed
    return indexed(subject, files('producers').joinpath('data/v8-word-laws'), 'v8-word/')
