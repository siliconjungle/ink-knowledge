#!/usr/bin/env python3
"""Compose source-bound representations using ordinary universal equations.

Each component preserves its own relation to the same logical state. All change
transitions run; one component supplies each public observation. The compiler
checks the complete product and does not trust this authoring strategy. A product
can cost more than either component, and is never selected without measurement.
"""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, identity
from ink_knowledge.store import entry, read
from representations import MATH, REP, refs, match
from action_replacement import var, call, cons, convert, trans


def generate(model, requests, directory, observers=None, share_observation=False):
    observers = observers or {}
    if not 2 <= len(requests) <= 8:
        raise ValueError('product requires two to eight components')
    objects = dict(model['objects'])
    plans = []
    for request in requests:
        if request['input_core_sha256'] != model['source']:
            raise ValueError('product source mismatch')
        plan = request['knowledge']['objects'][request['representation']]['payload']
        if plan['logical_state'] != {'Data': model['state']} or sorted(plan['actions']) != sorted(model['actions']):
            raise ValueError('product requires exact common source state and actions')
        if plan['source_objects'] != sorted(model['objects']):
            raise ValueError('product source-definition mismatch')
        for key, value in request['knowledge']['objects'].items():
            if key in objects and objects[key] != value:
                raise ValueError('conflicting component object')
            objects[key] = value
        plans.append(plan)
    if sum(len(p['relations']) for p in plans) > 8:
        raise ValueError('product relation limit')
    if any(name not in model['actions'] or not 0 <= i < len(plans)
           for name, i in observers.items()):
        raise ValueError('invalid product observer')

    def add(declaration, extra=()):
        body = next(iter(declaration.values()))
        payload = {'declaration': declaration}
        value = entry('theorem' if 'Theorem' in declaration else 'definition', MATH,
                      payload, refs(payload) | set(extra), parameters=dict(body.get('params', [])),
                      result=body.get('result'), conditions=body.get('conditions', []))
        key = identity(value)
        objects[key] = value
        return key

    def function(params, result, body, recursive=None):
        return add({'Function': dict(params=params, result=result, body=body, recursive=recursive)})

    def theorem(params, conditions, left, right, proof):
        return add({'Theorem': dict(params=params, conditions=conditions,
                                    **{'from': left, 'to': right}, proof=proof)},
                   [key for key, value in objects.items()
                    if 'Datatype' in value['payload'].get('declaration', {})])

    def use(key, args, premises=()):
        return {'Use': dict(theorem=key, arguments=args, premises=list(premises))}

    def equation(left, right):
        return {'from': left, 'to': right}

    def rel(relation, physical, logical):
        return [call(relation[side], [physical, logical]) for side in ['left', 'right']]

    logical = {'Data': model['state']}
    datatype = add({'Datatype': dict(constructors=[dict(name='Product', fields=[p['physical_state'] for p in plans])])})
    physical = {'Data': datatype}
    names = ['component_' + str(i) for i in range(len(plans))]
    getters = [function([['physical', physical]], p['physical_state'],
                        match(var('physical'), [(names, var(names[i]))]), recursive=0)
               for i, p in enumerate(plans)]
    # Structural declarations with no recursive calls are total. On symbolic
    # inputs the existing checker keeps these projections opaque; on constructor
    # inputs it computes them literally. This bounds composition without adding
    # a new reduction or proof rule.
    select = lambda i, x: call(getters[i], [x])
    encode = function([['logical', logical]], physical,
                      cons(datatype, 0, [call(p['encode'], [var('logical')]) for p in plans]))
    decode = function([['physical', physical]], logical,
                      call(plans[0]['decode'], [select(0, var('physical'))]))

    relations, initialisation, component_conditions = [], [], []
    offsets = []
    for i, plan in enumerate(plans):
        offsets.append(len(relations))
        conditions = [equation(*rel(r, var('physical'), var('logical'))) for r in plan['relations']]
        component_conditions.append(conditions)
        for j, relation in enumerate(plan['relations']):
            signature = objects[relation['left']]['payload']['declaration']['Function']['result']
            product_relation = {side: function([['physical', physical], ['logical', logical]], signature,
                                               call(relation[side], [select(i, var('physical')), var('logical')]))
                                for side in ['left', 'right']}
            relations.append(product_relation)
            before = rel(relation, call(plan['encode'], [var('logical')]), var('logical'))
            lemma = theorem([['logical', logical]], [], *before, plan['initialisation'][j])
            after = rel(product_relation, call(encode, [var('logical')]), var('logical'))
            initialisation.append(trans(convert(after[0], before[0]), use(lemma, [var('logical')]), convert(before[1], after[1])))

    snapshot_lemma = theorem([['physical', plans[0]['physical_state']], ['logical', logical]],
                             component_conditions[0], call(plans[0]['decode'], [var('physical')]),
                             var('logical'), plans[0]['snapshot'])
    premises = lambda i: [{'Hypothesis': offsets[i] + j} for j in range(len(plans[i]['relations']))]
    start = call(decode, [var('physical')])
    snapshot = trans(convert(start, call(plans[0]['decode'], [select(0, var('physical'))])),
                     use(snapshot_lemma, [select(0, var('physical')), var('logical')], premises(0)))
    actions = {}
    for name, source in model['actions'].items():
        rest = source['params'][1:]
        args = [var(n) for n, _ in rest]
        original = call(source['function'], [var('logical'), *args])
        post = match(original, [(['post_reply', 'post_commit', 'post_version', 'post_state', 'post_events'], var('post_state')),
                                (['post_error', 'post_version', 'post_state'], var('post_state'))])
        results = [p['actions'][name]['result'] for p in plans]
        result_id = add({'Datatype': dict(constructors=[dict(name='ProductTransition', fields=results)])})
        result = {'Data': result_id}
        result_names = ['result_' + str(i) for i in range(len(plans))]
        results_get = [function([['executed', result]], sort,
                               match(var('executed'), [(result_names, var(result_names[i]))]))
                       for i, sort in enumerate(results)]
        execute = function([['physical', physical], *rest], result,
                           cons(result_id, 0, [call(p['actions'][name]['execute'], [select(i, var('physical')), *args])
                                               for i, p in enumerate(plans)]))
        next_function = function([['executed', result]], physical,
                                 cons(datatype, 0, [call(p['actions'][name]['next'], [call(results_get[i], [var('executed')])])
                                                    for i, p in enumerate(plans)]))
        chosen = observers.get(name, 0)
        observe = function([['executed', result]], source['result'],
                           call(plans[chosen]['actions'][name]['observe'], [call(results_get[chosen], [var('executed')])]))
        executed = call(execute, [var('physical'), *args])
        observed = call(observe, [executed])
        preservation = []
        observation = None
        for i, plan in enumerate(plans):
            action = plan['actions'][name]
            base_executed = call(action['execute'], [var('physical'), *args])
            base_next = call(action['next'], [base_executed])
            params = [['physical', plan['physical_state']], ['logical', logical], *rest]
            if i == chosen:
                before = call(action['observe'], [base_executed])
                lemma = theorem(params, component_conditions[i], before, original, action['observation'])
                target = call(action['observe'], [call(action['execute'], [select(i, var('physical')), *args])])
                observation = trans(convert(observed, target),
                                    use(lemma, [select(i, var('physical')), var('logical'), *args], premises(i)))
            for j, relation in enumerate(plan['relations']):
                left, right = rel(relation, base_next, post)
                lemma = theorem(params, component_conditions[i], left, right, action['preservation'][j])
                selected_next = call(action['next'], [call(action['execute'], [select(i, var('physical')), *args])])
                before = rel(relation, selected_next, post)
                after = rel(relations[offsets[i] + j], call(next_function, [executed]), post)
                preservation.append(trans(convert(after[0], before[0]),
                                          use(lemma, [select(i, var('physical')), var('logical'), *args], premises(i)),
                                          convert(before[1], after[1])))
        actions[name] = dict(execute=execute, result=result, next=next_function, observe=observe,
                             observation=observation, preservation=preservation)
    if share_observation:
        from shared_product import share
        share(model, plans, actions, physical, getters, relations, offsets, objects, function, theorem, observers)
    plan = dict(source_objects=sorted(model['objects']), logical_state=logical,
                physical_state=physical, encode=encode, decode=decode, relations=relations,
                initialisation=initialisation, snapshot=snapshot, actions=actions)
    value = entry('representation', REP, plan, refs(plan), parameters={'logical': logical},
                  result=physical, effects=['source-transitions'])
    value['interface']['operations'] = sorted(actions)
    key = identity(value)
    objects[key] = value
    store = Store.publish(directory, objects.values(), {'representations/product': key})
    return dict(schema=1, semantics=REP, input_core_sha256=model['source'],
                representation=key, knowledge=store.bundle([key]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model', type=Path)
    parser.add_argument('components', nargs='+', type=Path)
    parser.add_argument('--observer', action='append', default=[], help='ACTION=zero-based component index')
    parser.add_argument('--shared', action='store_true', help='prove one shared observation across cache transitions')
    parser.add_argument('-o', '--output', required=True, type=Path)
    args = parser.parse_args()
    observers = dict((name, int(index)) for name, index in (x.split('=', 1) for x in args.observer))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    product = generate(read(args.model), [read(p) for p in args.components],
                       args.output.parent / 'database', observers, args.shared)
    args.output.write_text(json.dumps(product, indent=2) + '\n')


if __name__ == '__main__':
    main()
