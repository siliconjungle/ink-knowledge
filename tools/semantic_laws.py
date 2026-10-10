#!/usr/bin/env python3
"""Produce example data for the general semantic equality checker. No authority.
All transformations are catalogue objects. The compiler contains none of these
patterns; new objects can be added without rebuilding it or this producer.
"""
import argparse
import hashlib
import json
from pathlib import Path

SEMANTICS = 'ink-conditional-laws-v1'
def value(t): return {'Value': t}
def arrow(a, b): return {'Arrow': [a, b]}
def term(sort, node): return dict(sort=sort, node=node)
def var(s, n): return term(s, {'Free': n})
def bound(s, i): return term(s, {'Bound': i})
def word(t, n): return term(value(t), {'Word': n})
def nat(n): return term('Nat', {'Nat': n})
def op(s, n, *a): return term(s, {'Op': [n, list(a)]})
def lam(s, body): return term(arrow(s, body['sort']), {'Lambda': body})
def binary(n, a, b): return op(a['sort'], 'binary:' + n, a, b)
def identity(v):
    # Law field order mirrors the versioned Rust wire struct. Named maps sort.
    return hashlib.sha256(json.dumps(v, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()
def law(params, a, b, proof='Normalize', conditions=(), dependencies=()):
    return dict(schema=1, semantics=SEMANTICS, params=dict(sorted(params.items())),
                conditions=list(conditions), **{'from': a, 'to': b}, proof=proof,
                dependencies=list(dependencies))
def examples():
    laws = []
    for t in ('U32', 'U64', 'I32'):
        s = value(t); x = var(s, 'x'); y = var(s, 'y')
        laws += [law({'x': s}, binary('+', x, word(t, 0)), x),
                 law({'x': s}, binary('*', x, word(t, 1)), x),
                 law({'x': s}, binary('-', x, x), word(t, 0)),
                 law({'x': s}, binary('+', x, x), binary('*', x, word(t, 2)))]
        a = var(s, 'a'); b = var(s, 'b')
        laws += [law({'x': s}, binary('+', binary('+', x, x), x), binary('*', x, word(t, 3))),
                 law({'x': s, 'a': s}, binary('+', binary('*', x, a), x),
                     binary('*', x, binary('+', a, word(t, 1)))),
                 law({'x': s, 'a': s, 'b': s}, binary('+', binary('*', x, a), binary('*', x, b)),
                     binary('*', x, binary('+', a, b)))]
        # A universal natural induction theorem, not a fixed-count recogniser.
        n = var('Nat', 'n'); k = var(s, 'k')
        body = binary('+', bound(s, 0), k)
        loop = op(s, 'call:repeat', n, x, lam(value('U32'), lam(s, body)))
        result = binary('+', x, binary('*', op(s, 'nat.word', n), k))
        proof = {'Induction': dict(variable='n', names=['step_count'], base='Normalize', step='Normalize')}
        laws.append(law({'n': 'Nat', 'x': s, 'k': s}, loop, result, proof))
        # Explicit premise. Useful only when the application proves y == 0.
        equation = dict(**{'from': y, 'to': word(t, 0)})
        condition = dict(**{'from': op(value('Bool'), 'binary:==', y, word(t, 0)),
                            'to': term(value('Bool'), {'Bool': True})})
        proof = {'AssertEquality': dict(equality=equation, premise={'Hypothesis': 0}, body='Normalize')}
        laws.append(law({'x': s, 'y': s}, binary('+', x, y), x, proof,
                        conditions=[condition]))
    for t in ('U32', 'U64', 'I32', 'F32', 'Bool'):
        s = value(t); ls = value({'List': t}); xs = var(ls, 'xs')
        fs = arrow(s, s); f = var(fs, 'f'); g = var(fs, 'g')
        first = op(ls, 'method:map', xs, f)
        twice = op(ls, 'method:map', first, g)
        composed = lam(s, op(s, 'apply', g, op(s, 'apply', f, bound(s, 0))))
        fused = op(ls, 'method:map', xs, composed)
        induction = {'Induction': dict(variable='xs', names=['head', 'tail'], base='Normalize', step='Normalize')}
        laws.append(law({'xs': ls, 'f': fs, 'g': fs}, twice, fused, induction))
        identity_map = op(ls, 'method:map', xs, lam(s, bound(s, 0)))
        laws.append(law({'xs': ls}, identity_map, xs, induction))
        c = var(value('Bool'), 'c'); x = var(s, 'x')
        laws.append(law({'c': value('Bool'), 'x': s}, op(s, 'call:choose', c, x, x), x))
    return laws

def main():
    a = argparse.ArgumentParser(); a.add_argument('-o', type=Path, required=True); args = a.parse_args()
    laws = examples(); objects = {identity(x): x for x in laws}
    catalogue = dict(schema=1, semantics=SEMANTICS, roots=list(objects), objects=dict(sorted(objects.items())))
    args.o.parent.mkdir(parents=True, exist_ok=True)
    args.o.write_text(json.dumps(catalogue, indent=2) + '\n')
    print(json.dumps(dict(laws=len(objects), catalogue=str(args.o))))
if __name__ == '__main__': main()
