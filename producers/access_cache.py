"""Untrusted point-cache discovery from source-bound access descriptions.

Descriptions guide search only. Existing source/action preservation equations
prove every proposed repair; no access description is a mathematical premise.
"""
import argparse
import json
from pathlib import Path

SEMANTICS = 'ink-action-access-v1'


def validate(model, access):
    if (access.get('schema') != 1 or access.get('semantics') != SEMANTICS
            or access.get('source') != model['source']):
        raise ValueError('access description source/semantics mismatch')
    if set(access.get('actions', {})) != set(model['actions']):
        raise ValueError('access description action coverage mismatch')


def discover(model, access):
    """Bounded discovery hints. The producer/checker can still decline a query."""
    validate(model, access)
    queries = []
    for name, summary in sorted(access['actions'].items()):
        if summary['kind'] != 'Query' or summary['parameters']:
            continue
        reads = summary['accesses']
        if not reads or any(a['mode'] != 'read' or a['conditions'] for a in reads):
            continue
        points = [a['scope'].get('Point', {}) for a in reads]
        if any(p.get('key_type') != 'U64' or set(p.get('key', {})) != {'Number'} for p in points):
            continue
        if len({(a['root'], p['key']['Number']) for a, p in zip(reads, points)}) != 1:
            continue
        queries.append(name)
    return queries


def decisions(model, access, query):
    if query not in discover(model, access):
        raise ValueError('query has no supported unconditional fixed-u64 point description')
    root = access['actions'][query]['accesses'][0]['root']
    result = {}
    for name, summary in sorted(access['actions'].items()):
        writes = [a for a in summary['accesses'] if a['root'] == root and a['mode'] == 'write']
        precise = bool(writes) and all(a['scope'].get('Point', {}).get('key_type') == 'U64' for a in writes)
        result[name] = dict(eligible=precise, writes=writes,
            reason=('point writes; propose guarded repair and other-key reuse' if precise
                    else 'no writes to query root' if not writes
                    else 'whole-root or unsupported-key write; refresh fallback'))
    return result


def setup(model, cache, add, objects, access, query):
    from producers.point_delta_dynamic import setup as dynamic_setup
    from producers.point_delta import binary, choice, match, replace, lift
    from producers.action_replacement import var, call, cons, trans
    from producers.cache_maintenance import cases
    choices = decisions(model, access, query)
    if not any(d['eligible'] for d in choices.values()):
        raise ValueError('no precise point writes for cache maintenance')
    reply=cache['case']['normal'].get('Construct',{}).get('arguments',[{}])[0]
    if 'Call' not in reply or not any(reply['Call']['function']==t['get'] for t in model['tables']):
        raise ValueError('access-guided tactic currently maintains raw point gets; mapped queries retain other candidates')
    # Existing induction/Boolean/bitvector laws establish exact key locality.
    # Even forged descriptions cannot supply proof premises or change this model.
    delta = dynamic_setup(model, cache, add, objects)
    index, q, table = delta['index'], delta['q'], delta['table']
    getof = lambda rows: call(delta['get'], [rows,q])
    none = cons(delta['option'],0,[])
    def recipe(rows, old, bindings):
        if rows == var(bindings[index]):return old
        if 'If' in rows:
            branch=rows['If']
            return choice(branch['condition'],recipe(branch['on_true'],old,bindings),recipe(branch['on_false'],old,bindings))
        update=rows.get('Call',{});args=update.get('arguments',[])
        name=next((n for n in delta['laws'] if table[n]==update.get('function')),None)
        if name is None or len(args)<2:raise ValueError('unsupported point update')
        prior=recipe(args[0],old,bindings)
        same=(none if name=='remove' else match(prior,[([],none),(['dynamic_old'],delta['some'](args[2]))])
              if name=='replace' else getof(rows))
        return choice(binary('==',args[1],q),same,prior)
    def equality(rows,bindings,facts=()):
        if rows==var(bindings[index]):return {'Refl':getof(rows)}
        if 'If' in rows:
            # Conditional state expressions (including ordinary upserts) compose
            # by ordinary Boolean cases, retaining the surrounding hypotheses.
            return cases(rows,getof,lambda r:recipe(r,getof(var(bindings[index])),bindings),
                hypotheses=len(facts),leaf_proof=lambda r,fs:equality(r,bindings,(*facts,*fs)))
        update=rows['Call'];args=update['arguments']
        name=next(n for n in delta['laws'] if table[n]==update['function'])
        prior=getof(args[0])
        same=(none if name=='remove' else match(prior,[([],none),(['dynamic_old'],delta['some'](args[2]))])
              if name=='replace' else getof(rows))
        context=choice(binary('==',args[1],q),same,prior)
        return trans({'Use':dict(theorem=delta['laws'][name],arguments=args,premises=[])},
                     lift(equality(args[0],bindings,facts),replace(context,prior,var('delta_hole'))))
    names = {a['function']: name for name, a in model['actions'].items()}
    def propose(sa):
        name = names.get(sa['function'])
        if not choices.get(name, {}).get('eligible'):return None
        def predict(t):
            if 'If' in t:
                b=t['If'];return choice(b['condition'],predict(b['on_true']),predict(b['on_false']))
            observation=t['Construct']
            if observation['constructor']!=0 or observation['arguments'][1]!={'Bool':True}:return var('cached_reply')
            return recipe(observation['arguments'][3]['Construct']['arguments'][index],var('cached_reply'),sa['case']['bindings'])
        try:return predict(sa['case']['normal'])
        except (ValueError,KeyError):return None
    return {**delta, 'action': propose, 'recipe':recipe,'equality':equality,'contextual_equality':True}


def main():
    from producers.representations import generate
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model', type=Path)
    parser.add_argument('--access', required=True, type=Path)
    parser.add_argument('--query', required=True)
    parser.add_argument('-o', '--output', required=True, type=Path)
    args = parser.parse_args()
    model = json.loads(args.model.read_bytes())
    access = json.loads(args.access.read_bytes())
    choices = decisions(model, access, args.query)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    proposal = generate(model, args.output.parent/'database', cache_query=args.query,
                        preserve_cache=True, access=access)
    request=proposal['requests'][1]
    plan=request['knowledge']['objects'][request['representation']]['payload']
    for name,decision in choices.items():
        decision['strategy']=('guarded maintenance' if decision['eligible'] and
            plan['actions'][name]['result']!=model['actions'][name]['result']
            else 'refresh fallback' if access['actions'][name]['kind']=='Change' else 'query')
    args.output.write_text(json.dumps(request, indent=2)+'\n')
    args.output.with_suffix('.discovery.json').write_text(json.dumps(dict(
        source=model['source'], query=args.query, actions=choices,
        trust='Discovery hints only; universal source/action equations grant admission.'), indent=2)+'\n')


if __name__ == '__main__':
    main()
