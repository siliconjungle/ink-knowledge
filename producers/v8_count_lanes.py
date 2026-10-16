"""Checked U64 count decompositions into fixed U32 operations.

V8's 32-bit Wasm int64 lowering motivates the split. These are ordinary source
alternatives, independent of the compiler and target. Profitability is measured
for the complete caller; sparse/zero inputs can favor the original operation.
"""
from importlib.resources import files
from .semantic_laws import value, var, word, op, bound
from .v8_integer_laws import bindings

UPSTREAM_REVISION = 'c4e049d3cbda775e2c3af9410f6e18b18388d68b'


def templates():
    u64, u32, boolean = value('U64'), value('U32'), value('Bool')
    x = var(u64, 'x')
    narrow = lambda a: op(u32, 'call:word_narrow_u64_to_u32', a)
    high = lambda a: narrow(op(u64, 'call:wrapping_shr', a, word('U32', 32)))
    count = lambda name, a: op(u32, 'call:' + name, a)
    add = lambda a, b: op(u32, 'binary:+', a, b)
    eq = lambda a, b: op(boolean, 'binary:==', a, b)
    choose = lambda c, a, b: op(u32, 'call:choose', c, a, b)

    def split(name, a):
        if name == 'popcount':
            return add(count(name, narrow(a)), count(name, high(a)))
        # The outer input has index 1 inside the half-word binding. Only the
        # selected count executes; the strict original input executes once.
        if name == 'leading_zeros':
            return bindings([u32], [high(a)], lambda hi:
                choose(eq(hi[0], word('U32', 0)),
                       add(word('U32', 32), count(name, narrow(bound(u64, 1)))),
                       count(name, hi[0])))
        return bindings([u32], [narrow(a)], lambda lo:
            choose(eq(lo[0], word('U32', 0)),
                   add(word('U32', 32), count(name, high(bound(u64, 1)))),
                   count(name, lo[0])))

    def guarded(name, a, sparse):
        target = split(name, a)
        if name == 'trailing_zeros':
            odd = op(boolean, 'binary:!=',
                     op(u64, 'call:word_and', a, word('U64', 1)), word('U64', 0))
            target = choose(odd, word('U32', 0), target)
        if sparse:
            cleared = op(u64, 'call:word_and', a,
                         op(u64, 'binary:-', a, word('U64', 1)))
            target = choose(eq(cleared, word('U64', 0)), word('U32', 1), target)
        return choose(eq(a, word('U64', 0)),
                      word('U32', 0 if name == 'popcount' else 64), target)

    rows = []
    for label, name, guard, sparse in [
            ('popcount', 'popcount', False, False),
            ('leading_zeros', 'leading_zeros', False, False),
            ('trailing_zeros', 'trailing_zeros', False, False),
            ('popcount_zero', 'popcount', True, False),
            ('popcount_sparse', 'popcount', True, True),
            ('leading_zeros_zero', 'leading_zeros', True, False),
            ('trailing_zeros_zero_odd', 'trailing_zeros', True, False)]:
        target = bindings([u64], [x], lambda args:
            guarded(name, args[0], sparse) if guard else split(name, args[0]))
        rows.append(dict(name=label, goal=dict(params={'x': u64}, conditions=[],
                         **{'from': count(name, x), 'to': target})))
    return rows


def specialize(subject, core):
    from .frozen_laws import specialize as indexed
    return indexed(subject, files('producers').joinpath('data/v8-count-lanes'),
                   'v8-count-lanes/')
