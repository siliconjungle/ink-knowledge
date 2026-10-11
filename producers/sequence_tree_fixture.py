#!/usr/bin/env python3
"""Publish a row-parametric sequence-tree definition/proof development fixture."""
import argparse
import copy
import json
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, identity
from ink_knowledge.store import entry
from representations import refs
from sequence_tree import define, D, U
from action_replacement import var, call, cons


def generate(directory, proofs=False):
    objects, carriers = {}, []
    def add(declaration, extra=()):
        declaration=copy.deepcopy(declaration)
        body = next(iter(declaration.values()))
        dependencies = refs(declaration) | set(extra)
        # Match scrutinees do not carry a type annotation. Each development
        # entry pins the small, fixed family of datatypes explicitly.
        if 'Datatype' not in declaration:
            dependencies |= set(carriers)
        obj = entry('theorem' if 'Theorem' in declaration else 'definition',
                    'first-order-inductive-equality-v1', {'declaration': declaration},
                    dependencies, parameters=dict(body.get('params', [])),
                    result=body.get('result'), conditions=body.get('conditions', []))
        key = identity(obj)
        objects[key] = obj
        if 'Datatype' in declaration:
            carriers.append(key)
        return key
    table = add({'Datatype': {'constructors': [
        {'name': 'Nil', 'fields': []},
        {'name': 'Cons', 'fields': ['U64', 'U64', 'SelfType']},
    ]}})
    option = add({'Datatype': {'constructors': [
        {'name': 'None', 'fields': []}, {'name': 'Some', 'fields': ['U64']},
    ]}})
    names = define(table, 'U64', option, add)
    names.update(table=table, option=option)
    if proofs:
        from sequence_tree_proofs import prove
        prove(names,objects,add,'U64')
    pending=list(names.values());reachable=set()
    while pending:
        key=pending.pop()
        if key in reachable:continue
        reachable.add(key);pending.extend(objects[key]['dependencies'])
    store = Store.publish(directory, [objects[key]for key in sorted(reachable)], names)
    (Path(directory)/'view.json').write_text(json.dumps(store.bundle(sorted(set(names.values()))), separators=(',', ':'))+'\n')
    (Path(directory)/'names.json').write_text(json.dumps(names, indent=2)+'\n')
    return names


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--proofs', action='store_true')
    args = parser.parse_args()
    print(json.dumps(generate(args.output,args.proofs)))
