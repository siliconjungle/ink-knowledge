#!/usr/bin/env python3
"""Ordinary untrusted proofs for observations of finite list constructors."""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, canonical, identity, semantic_entry
from semantic_laws import bound, lam, law, op, term, value, var, word


def examples():
    result = {}
    for kind in ('U32', 'U64', 'I32', 'F32', 'Bool'):
        element, sequence = value(kind), value({'List': kind})
        for size in range(9):
            params = {f'x{i}': element for i in range(size)}
            items = [var(element, f'x{i}') for i in range(size)]
            literal = term(sequence, 'Nil')
            for item in reversed(items):
                literal = term(sequence, {'Cons': [item, literal]})
            prefix = f'literal-list/{kind.lower()}-{size}'
            result[prefix + '-length'] = law(params, op(value('U32'), 'call:length', literal), word('U32', size))
            result[prefix + '-count'] = law(params, op(value('U64'), 'call:count', literal), word('U64', size))
            fallback = var(element, 'fallback')
            reads = dict(params, fallback=element)
            result[prefix + '-outside'] = law(reads, op(element, 'method:at_or', literal, word('U32', size), fallback), fallback)
            if size:
                result[prefix + '-first'] = law(reads, op(element, 'method:at_or', literal, word('U32', 0), fallback), items[0])
            if kind in ('U32', 'U64', 'I32'):
                item, rest = bound(element, 1), bound(element, 0)
                predicate = op(value('Bool'), 'binary:!=', item, word(kind, 0))
                callback = lam(element, lam(element, op(element, 'call:choose', predicate, item, rest)))
                selected = fallback
                for x in reversed(items):
                    predicate = op(value('Bool'), 'binary:!=', x, word(kind, 0))
                    selected = op(element, 'call:choose', predicate, x, selected)
                result[prefix + '-first-nonzero'] = law(reads, op(element, 'call:foldr', literal, fallback, callback), selected)
    return result


def publish(output):
    output = Path(output)
    names, objects, roots = {}, [], []
    if (output / 'store/snapshot.json').exists():
        previous = Store(output)
        objects = [previous.object(i) for i in previous.members()]
        names = json.loads((output / 'store/names.json').read_text())
        view = output / 'store/rewrite-view.json'
        if view.exists():
            roots = json.loads(view.read_text())['roots']
    added = []
    for name, proof in examples().items():
        entry = semantic_entry(proof)
        key = identity(entry)
        objects.append(entry)
        names['rewrite/' + name] = key
        roots.append(key)
        added.append(key)
    store = Store.publish(output, objects, names)
    store.rebuild()
    (output / 'store/rewrite-view.json').write_bytes(canonical(store.bundle(sorted(set(roots)))) + b'\n')
    (output / 'store/literal-collection-view.json').write_bytes(canonical(store.bundle(added)) + b'\n')
    return store


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-store', required=True, type=Path)
    args = parser.parse_args()
    store = publish(args.output_store)
    print(json.dumps({'laws': len(examples()), 'snapshot': store.snapshot_id}))
