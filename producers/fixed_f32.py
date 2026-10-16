"""Untrusted closed binary32 proposals using exact integer arithmetic.

Every proposed result still needs ordinary kernel conversion. No host floating
arithmetic, reassociation, identity for a dynamic operand, or truth cache is used.
"""
from math import isqrt

MASK = (1 << 32) - 1
NAN = 0x7fc00000
INF = 0x7f800000


def _parts(bits):
    sign = bits >> 31
    exponent = bits >> 23 & 255
    fraction = bits & 0x7fffff
    return sign, exponent, fraction


def _finite(bits):
    sign, exponent, fraction = _parts(bits)
    return sign, fraction if exponent == 0 else fraction | (1 << 23), -149 if exponent == 0 else exponent - 150


def _nearest(numerator, denominator):
    quotient, remainder = divmod(numerator, denominator)
    return quotient + int(2 * remainder > denominator or (2 * remainder == denominator and quotient & 1))


def _encode(sign, numerator, denominator=1, exponent=0):
    """Round sign * numerator / denominator * 2**exponent, ties to even."""
    if numerator == 0:
        return sign << 31
    power = numerator.bit_length() - denominator.bit_length()
    if (numerator << max(-power, 0)) < (denominator << max(power, 0)):
        power -= 1
    quantum = max(power + exponent - 23, -149)
    shift = exponent - quantum
    value = _nearest(numerator << max(shift, 0), denominator << max(-shift, 0))
    if value == 0:
        return sign << 31
    power = value.bit_length() - 1 + quantum
    if power > 127:
        return (sign << 31) | INF
    if power < -126:
        return (sign << 31) | value
    significand = value >> max(value.bit_length() - 24, 0)
    return (sign << 31) | ((power + 127) << 23) | (significand & 0x7fffff)


def evaluate(op, a, b=0):
    """Return a proposed MathTerm for one known fixed primitive, or None."""
    if any(type(x) is not int or not 0 <= x < 1 << 64 for x in (a, b)):
        raise ValueError('fixed scalar operand outside word range')
    if op in ('f32:from_u32', 'f32:from_u64', 'f32:from_i32'):
        value = a if op == 'f32:from_u64' else a & MASK
        negative = op == 'f32:from_i32' and bool(value & (1 << 31))
        return {'U64': _encode(int(negative), (1 << 32) - value if negative else value)}
    a &= MASK; b &= MASK
    sa, ea, fa = _parts(a); sb, eb, fb = _parts(b)
    nan_a, nan_b = ea == 255 and fa != 0, eb == 255 and fb != 0
    inf_a, inf_b = ea == 255 and fa == 0, eb == 255 and fb == 0
    zero_a, zero_b = a & 0x7fffffff == 0, b & 0x7fffffff == 0
    if op == 'f32:neg':
        return {'U64': a ^ (1 << 31)}
    if op in ('f32:is_nan', 'f32:is_finite'):
        return {'Bool': nan_a if op == 'f32:is_nan' else ea != 255}
    if op in ('f32:==', 'f32:!=', 'f32:<', 'f32:<=', 'f32:>', 'f32:>='):
        equal = not (nan_a or nan_b) and (a == b or zero_a and zero_b)
        key = lambda bits: (~bits & MASK) if bits >> 31 else bits ^ (1 << 31)
        less = not (nan_a or nan_b or equal) and key(a) < key(b)
        greater = not (nan_a or nan_b or equal) and key(a) > key(b)
        return {'Bool': {'f32:==': equal, 'f32:!=': not equal, 'f32:<': less,
            'f32:<=': less or equal, 'f32:>': greater, 'f32:>=': greater or equal}[op]}
    if op in ('f32:floor', 'f32:ceil', 'f32:trunc', 'f32:round_ties_even'):
        if nan_a: return {'U64': NAN}
        if inf_a or zero_a: return {'U64': a}
        _, magnitude, exponent = _finite(a)
        if exponent >= 0: return {'U64': a}
        integral, remainder = divmod(magnitude, 1 << -exponent)
        if op == 'f32:floor': integral += int(sa and remainder != 0)
        if op == 'f32:ceil': integral += int(not sa and remainder != 0)
        if op == 'f32:round_ties_even': integral = _nearest(magnitude, 1 << -exponent)
        return {'U64': _encode(sa, integral)}
    if op == 'f32:sqrt':
        if nan_a or sa and not zero_a: return {'U64': NAN}
        if inf_a or zero_a: return {'U64': a}
        _, magnitude, exponent = _finite(a)
        power = (magnitude.bit_length() - 1 + exponent) // 2
        quantum = max(power - 23, -149)
        shift = exponent - 2 * quantum
        numerator, denominator = magnitude << max(shift, 0), 1 << max(-shift, 0)
        integral = isqrt(numerator // denominator)
        delta = 4 * numerator - denominator * (2 * integral + 1) ** 2
        integral += int(delta > 0 or delta == 0 and integral & 1)
        return {'U64': _encode(0, integral, exponent=quantum)}
    if op not in ('f32:+', 'f32:-', 'f32:*', 'f32:div'):
        return None
    if nan_a or nan_b: return {'U64': NAN}
    if op in ('f32:+', 'f32:-'):
        if op == 'f32:-': sb ^= 1
        if inf_a or inf_b:
            return {'U64': NAN if inf_a and inf_b and sa != sb else ((sa if inf_a else sb) << 31) | INF}
        _, ma, xa = _finite(a); _, mb, xb = _finite(b)
        exponent = min(xa, xb)
        total = (-1 if sa else 1) * (ma << (xa-exponent)) + (-1 if sb else 1) * (mb << (xb-exponent))
        sign = int(total < 0) if total else int(zero_a and zero_b and sa and sb)
        return {'U64': _encode(sign, abs(total), exponent=exponent)}
    sign = sa ^ sb
    if op == 'f32:*':
        if inf_a and zero_b or inf_b and zero_a: return {'U64': NAN}
        if inf_a or inf_b: return {'U64': (sign << 31) | INF}
        _, ma, xa = _finite(a); _, mb, xb = _finite(b)
        return {'U64': _encode(sign, ma * mb, exponent=xa+xb)}
    if inf_a and inf_b or zero_a and zero_b: return {'U64': NAN}
    if inf_a or zero_b: return {'U64': (sign << 31) | INF}
    if zero_a or inf_b: return {'U64': sign << 31}
    _, ma, xa = _finite(a); _, mb, xb = _finite(b)
    return {'U64': _encode(sign, ma, mb, xa-xb)}
