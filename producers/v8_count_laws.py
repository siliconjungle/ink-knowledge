"""External fixed-word count proposals; every equation needs ordinary V5 RUP.

The compiler interprets existing count primitives, independent of these patterns.
Constant-result replacements retain evaluation of the original count argument.
"""
from importlib.resources import files
from .semantic_laws import value, var, word, op
from .v8_integer_laws import bindings

UPSTREAM_REVISION = 'c4e049d3cbda775e2c3af9410f6e18b18388d68b'


def templates():
    rows = []
    u32, boolean = value('U32'), value('Bool')
    k = var(u32, 'k')
    for carrier, width in [('U32', 32), ('I32', 32), ('U64', 64)]:
        sort = value(carrier)
        x = var(sort, 'x')
        effective = op(u32, 'call:word_and', k, word('U32', width - 1))
        power = op(sort, 'call:wrapping_shl', word(carrier, 1), k)
        for name in ['popcount', 'leading_zeros', 'trailing_zeros']:
            count = lambda argument: op(u32, 'call:' + name, argument)
            test = op(boolean, 'binary:==', count(x),
                      word('U32', 0 if name == 'popcount' else width))
            rows.append(dict(name=carrier.lower() + '_' + name + '_zero_test',
                             goal=dict(params={'x': sort}, conditions=[],
                                       **{'from': test, 'to': op(boolean, 'binary:==', x, word(carrier, 0))})))
            if name == 'popcount':
                target = bindings([u32], [k], lambda arguments: word('U32', 1))
            elif name == 'trailing_zeros':
                target = effective
            else:
                target = op(u32, 'binary:-', word('U32', width - 1), effective)
            rows.append(dict(name=carrier.lower() + '_' + name + '_constructed_power',
                             goal=dict(params={'k': u32}, conditions=[],
                                       **{'from': count(power), 'to': target})))
    return rows


def specialize(subject, core):
    from .frozen_laws import specialize as indexed
    return indexed(subject, files('producers').joinpath('data/v8-count-laws'), 'v8-count/')
