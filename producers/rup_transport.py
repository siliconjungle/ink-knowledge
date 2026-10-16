"""Untrusted lossless RUP hint packaging; every decoded hint still needs replay.

This is independent of circuit/semantic modes. Packing changes proof identities,
never statements, reference order, budgets or admission/selection authority.
"""
import copy
from ink_knowledge import canonical

ALPHABET = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_'
MAX_HINTS = 100_000
MAX_REFERENCE = 320_000


def encode_hints(hints):
    if not hints or len(hints) > MAX_HINTS:
        raise ValueError('bounded nonempty hint sequence required')
    previous = 0
    output = []
    for reference in hints:
        if type(reference) is not int or not 0 <= reference < MAX_REFERENCE:
            raise ValueError('hint reference range')
        delta = reference - previous
        value = 2 * delta if delta >= 0 else -2 * delta - 1
        while value >= 32:
            output.append(ALPHABET[(value & 31) | 32])
            value >>= 5
        output.append(ALPHABET[value])
        previous = reference
    return ''.join(output)


def decode_hints(text):
    if type(text) is not str or not text or len(text) > 4 * MAX_HINTS:
        raise ValueError('packed hint byte limit')
    output = []
    value = shift = previous = 0
    for char in text:
        digit = ALPHABET.find(char)
        if digit < 0:
            raise ValueError('packed hint digit')
        value |= (digit & 31) << shift
        if digit & 32:
            shift += 5
            if shift >= 20:
                raise ValueError('packed hint digit limit')
            continue
        if shift and not digit:
            raise ValueError('noncanonical packed hint')
        previous += value // 2 if value % 2 == 0 else -(value // 2) - 1
        if not 0 <= previous < MAX_REFERENCE:
            raise ValueError('packed hint reference range')
        output.append(previous)
        if len(output) > MAX_HINTS:
            raise ValueError('packed hint count limit')
        value = shift = 0
    if shift:
        raise ValueError('truncated packed hint')
    return output


def unpack_certificate(certificate):
    result = copy.deepcopy(certificate)
    for step in result['steps']:
        if 'hint_deltas_v1' in step:
            if step['hints']:
                raise ValueError('both plain and packed hints')
            step['hints'] = decode_hints(step.pop('hint_deltas_v1'))
    return result


def pack_certificate(certificate):
    original = unpack_certificate(certificate)
    result = copy.deepcopy(original)
    for step in result['steps']:
        if not step['hints']:
            continue
        packed = dict(step, hints=[], hint_deltas_v1=encode_hints(step['hints']))
        if len(canonical(packed)) < len(canonical(step)):
            step.clear()
            step.update(packed)
    if unpack_certificate(result) != original:
        raise ValueError('hint transport changed reference sequence')
    return result if len(canonical(result)) < len(canonical(certificate)) else copy.deepcopy(certificate)
