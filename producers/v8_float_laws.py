"""Exact binary32 proposals; no fast math, payload erasure or range assumptions.

Fixed primitive interpretation lives in the general checker. These source laws
are data and still require independent RUP replay and measured selection.
"""
from importlib.resources import files
from .semantic_laws import value, var, word, term, op, lam


def templates():
    f32, u32, boolean = value('F32'), value('U32'), value('Bool')
    x, raw = var(f32, 'x'), var(u32, 'raw')
    bits = lambda x: op(u32, 'call:f32_bits', x)
    floating = lambda x: op(f32, 'call:f32_from_bits', x)
    neg = lambda x: op(f32, 'neg', x)
    nan = lambda x: op(boolean, 'call:is_nan', x)
    finite = lambda x: op(boolean, 'call:is_finite', x)
    invert = lambda x: op(boolean, 'binary:==', x, term(boolean, {'Bool': False}))
    flip = lambda x: op(u32, 'call:word_xor', x, word('U32', 0x80000000))
    false = term(boolean, {'Bool': False})
    # Retain evaluation of the source operand, including failed helpers or
    # contracts, even when the comparison's value is always false.
    strict_false = op(boolean, 'apply', lam(f32, false), x)
    rows = [
        ('float_bits_roundtrip', {'x': f32}, floating(bits(x)), x),
        ('word_bits_roundtrip', {'raw': u32}, bits(floating(raw)), raw),
        ('double_negation', {'x': f32}, neg(neg(x)), x),
        ('nan_negation', {'x': f32}, nan(neg(x)), nan(x)),
        ('finite_negation', {'x': f32}, finite(neg(x)), finite(x)),
        ('negated_bits', {'x': f32}, bits(neg(x)), flip(bits(x))),
        ('negated_from_bits', {'raw': u32}, neg(floating(raw)), floating(flip(raw))),
        ('nan_from_bits', {'raw': u32}, nan(floating(raw)),
         op(boolean, 'binary:>', op(u32, 'call:word_and', raw, word('U32', 0x7fffffff)), word('U32', 0x7f800000))),
        ('finite_from_bits', {'raw': u32}, finite(floating(raw)),
         op(boolean, 'binary:!=', op(u32, 'call:word_and', raw, word('U32', 0x7f800000)), word('U32', 0x7f800000))),
    ]
    for name in ['==', '!=', '<', '>', '<=', '>=']:
        result = nan(x) if name == '!=' else strict_false if name in ('<','>') else invert(nan(x))
        rows.append(('self_'+{'==':'equal','!=':'unequal','<':'less','>':'greater','<=':'le','>=':'ge'}[name],
                     {'x':f32},op(boolean,'binary:'+name,x,x),result))
    return [dict(name=name,goal=dict(params=params,conditions=[],**{'from':left,'to':right}))
            for name,params,left,right in rows]


def specialize(subject, core):
    from .frozen_laws import specialize as indexed
    return indexed(subject, files('producers').joinpath('data/v8-float-laws'), 'v8-float/')
