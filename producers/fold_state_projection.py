"""Untrusted source fold-state projection, with a universal step simulation.

Discovery proposes smaller ordinary source helpers. The existing general fold
law and exact source definition context must prove every replacement; syntactic
field liveness is never rewrite authority or profitability evidence.
"""
import copy
import json
from pathlib import Path
import subprocess
import tempfile

from ink_knowledge import Store, canonical, entry, identity, semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_planner.semantic_search import children, map_children, positions, replace, substitute
from producers.definitional_roundtrips import _beta, _substitute
from producers.definition_context28 import bind
from producers.semantic_laws import bound, lam, law, op, value, var
from producers.owned_fold_contracts import instantiate


def candidates(core, limit=16):
    """Bounded proposals for a record fold observed through one field.

    Other accumulator fields must be absent from the retained step expression.
    Keep all source let initializers in their original order. In particular,
    syntactic dead-binding removal cannot silently erase strict computations.
    """
    program = core['program']
    functions = {f['name']: f for f in program['functions']}
    records = program['records']
    rows = []
    for function in program['functions']:
        if len(rows) >= limit:
            break
        body = function['body']
        if (not isinstance(body, dict) or 'Let' not in body
                or len(canonical(body)) > 16384):
            continue
        local, _, initial, rest = body['Let']
        fold = initial.get('Call') if isinstance(initial, dict) else None
        if not fold or fold[0] != 'foldl' or len(fold[1]) != 3:
            continue
        xs, seed, callback = fold[1]
        if not isinstance(seed, dict) or 'Record' not in seed:
            continue
        record, fields = seed['Record']
        if record not in records or len(records[record]) < 2:
            continue
        if not isinstance(callback, dict) or 'Lambda' not in callback:
            continue
        item, inner = callback['Lambda']
        if not isinstance(inner, dict) or 'Lambda' not in inner:
            continue
        state, call = inner['Lambda']
        call = call.get('Call') if isinstance(call, dict) else None
        if not call or call[0] not in functions:
            continue
        step = functions[call[0]]
        if len(canonical(step['body'])) > 16384:
            continue
        owner_positions = [i for i, (_, t) in enumerate(step['params'])
                           if t == {'Named': record}]
        if (step['result'] != {'Named': record} or len(owner_positions) != 1
                or len(call[1]) != len(step['params'])):
            continue
        owner_index = owner_positions[0]
        owner = step['params'][owner_index][0]
        if call[1][owner_index] != {'Var': state}:
            continue
        for field, ty in records[record]:
            if len(rows) >= limit:
                break
            try:
                def projection(expr, root):
                    if not isinstance(expr, dict):
                        return copy.deepcopy(expr)
                    if expr.get('Field') == [{'Var': root}, field]:
                        return {'Var': root}
                    if expr == {'Var': root}:
                        raise ValueError('whole or other-field accumulator observation')
                    if 'Let' in expr and expr['Let'][0] == root:
                        raise ValueError('shadowed accumulator')
                    if 'Lambda' in expr and expr['Lambda'][0] == root:
                        raise ValueError('shadowed accumulator')
                    def descend(v):
                        if isinstance(v, dict):
                            return projection(v, root)
                        if isinstance(v, list):
                            return [descend(x) for x in v]
                        return copy.deepcopy(v)
                    return {k: descend(v) for k, v in expr.items()}

                def step_body(expr):
                    if not isinstance(expr, dict):
                        raise ValueError('unsupported step result')
                    if 'Let' in expr:
                        n, annotation, initial, tail = expr['Let']
                        if n == owner:
                            raise ValueError('shadowed accumulator')
                        return {'Let': [n, annotation, projection(initial, owner), step_body(tail)]}
                    if expr.get('Call', [None])[0] == 'choose':
                        condition, yes, no = expr['Call'][1]
                        return {'Call': ['choose', [projection(condition, owner),
                                                    step_body(yes), step_body(no)]]}
                    if expr == {'Var': owner}:
                        return {'Var': owner}
                    if 'Record' in expr and expr['Record'][0] == record:
                        return projection(dict(expr['Record'][1])[field], owner)
                    raise ValueError('unsupported step result')

                projected_rest = projection(rest, local)
                projected_body = step_body(step['body'])
                helper = dict(name='fold_step_' + identity([step, field])[:20],
                              params=copy.deepcopy(step['params']), result=ty, body=projected_body)
                helper['params'][owner_index][1] = ty
                callback = {'Lambda': [item, {'Lambda': [state,
                            {'Call': [helper['name'], copy.deepcopy(call[1])]}]}]}
                reduced = dict(name='fold_projected_' + identity([function, field])[:20],
                               params=copy.deepcopy(function['params']), result=function['result'],
                               body={'Let': [local, ty, {'Call': ['foldl', [copy.deepcopy(xs),
                                   copy.deepcopy(dict(fields)[field]), callback]]}, projected_rest]})
                if helper['name'] in functions or reduced['name'] in functions:
                    continue
                rows.append(dict(original=function, helper=reduced, step=helper, field=field))
            except (ValueError, KeyError):
                continue
    return rows


def prove(core, subject, left, right, projection_law, *, budget=16000):
    """Construct ordinary Use/Congruence evidence for one projected source fold.

    The simulation is quantified over arbitrary items and accumulator states,
    including states never visited by a training trace. The kernel checks it.
    """
    functions = {f['name']: f for f in core['program']['functions']}
    records = core['program']['records']
    declaration, other = functions[left], functions[right]
    if declaration['params'] != other['params'] or declaration['result'] != other['result']:
        raise ValueError('source signatures differ')
    remaining = [budget]

    def operation(t):
        return t['node'].get('Op') if isinstance(t['node'], dict) else None

    def expose(t):
        remaining[0] -= 1
        if remaining[0] < 0:
            raise ValueError('fold projection proposal work limit')
        if isinstance(t['node'], dict) and 'Lambda' in t['node']:
            return t
        c = operation(t)
        if c:
            name, args = c
            if name == 'call:foldl':
                return t
            if name.startswith('call:') and name[5:] in functions:
                f = functions[name[5:]]
                return expose(_substitute(subject['functions'][f['name']],
                                          dict(zip((n for n, _ in f['params']), args))))
            if name == 'apply' and isinstance(args[0]['node'], dict) and 'Lambda' in args[0]['node']:
                return expose(_beta(args[0]['node']['Lambda'], args[1]))
        t = map_children(t, expose)
        c = operation(t)
        if c and c[0].startswith('field:'):
            receiver = operation(c[1][0])
            if receiver and receiver[0].startswith('record:'):
                fields = records[receiver[0][7:]]
                i = next(i for i, (n, _) in enumerate(fields) if n == c[0][6:])
                return expose(receiver[1][i])
        return t

    params = {n: value(t) for n, t in declaration['params']}
    arguments = [var(params[n], n) for n, _ in declaration['params']]
    source = op(value(declaration['result']), 'call:' + left, *arguments)
    target = op(source['sort'], 'call:' + right, *arguments)
    a, b = expose(source), expose(target)
    old = [(p, t) for p, t in positions(a) if operation(t)
           and operation(t)[0].startswith('field:') and operation(operation(t)[1][0])
           and operation(operation(t)[1][0])[0] == 'call:foldl']
    new = [t for _, t in positions(b) if operation(t) and operation(t)[0] == 'call:foldl']
    if len(old) != 1 or len(new) != 1:
        raise ValueError('one directly observed fold per source required')
    path, observed = old[0]
    fold = operation(observed)[1][0]
    xs, initial, step = operation(fold)[1]
    small_xs, small_initial, reduced = operation(new[0])[1]
    if xs != small_xs:
        raise ValueError('fold input differs')
    project = lam(initial['sort'], op(observed['sort'], operation(observed)[0], bound(initial['sort'], 0)))
    key = identity(projection_law)
    types = dict(A=xs['sort']['Value']['List'], S=initial['sort']['Value'], R=observed['sort']['Value'])
    arguments = dict(xs=xs, initial=initial, project=project, step=step, reduced=reduced)
    instance = instantiate(projection_law['payload'], types)
    # Source elaboration may eta-expand callback parameters. Import the exact
    # instantiated endpoints; Normalize separately proves the source bridge.
    before = substitute(instance['from'], arguments)
    after = substitute(instance['to'], arguments)
    use = {'Use': dict(law=key, types=types, arguments=arguments,
                      premises=[], assumptions=['Normalize'])}
    proof = {'Trans': dict(middle=before, left='Normalize', right=use)}
    def lift(t, p):
        if not p:
            return proof
        return {'Congruence': [lift(c, p[1:]) if i == p[0] else 'Normalize'
                               for i, c in enumerate(children(t))]}
    rewritten = replace(a, path, after)
    result = law(params, source, target, {'Trans': dict(middle=a, left='Normalize', right={
        'Trans': dict(middle=rewritten, left=lift(a, path), right='Normalize')})},
                 dependencies=[key])
    result['semantics'] = 'ink-general-laws-v1'
    return bind(result, core, subject, [left, right])


def propose(context, limit=16):
    if context.get('representation'):
        return
    core = context['core']
    rows = candidates(core, limit)
    if not rows:
        return
    root = Path(context['knowledge_root'])
    store = Store(root, root / 'store/snapshots' / (context['knowledge_snapshot'] + '.json'))
    parent = Store(Path(__file__).resolve().parents[1] / 'libraries/proofs/fold-projection')
    key = parent.names['fold/project']
    general = parent.object(key)

    def invoke(*args):
        result = subprocess.run([context['compiler'], *map(str, args)], capture_output=True,
                                text=True, timeout=context.get('check_timeout', 120))
        if result.returncode:
            raise ValueError(result.stderr[-3000:])
        return json.loads(result.stdout) if result.stdout.lstrip().startswith(('{', '[')) else None

    with tempfile.TemporaryDirectory(prefix='ink-fold-projection-') as temporary:
        directory = Path(temporary)
        original = directory / 'original.json'
        original.write_bytes(canonical(core))
        # A separate extension per candidate keeps an inapplicable alternative
        # from changing another candidate's source identity or helper closure.
        for index, row in enumerate(rows):
            try:
                d = directory / str(index)
                d.mkdir()
                extension = entry('definition', 'ink-source-extension-v1', dict(
                    functions=[row['step'], row['helper']], records={}, enums={}, ids=[]))
                eid = identity(extension)
                request = dict(schema=1, semantics='ink-source-extension-v1',
                               input_core_sha256=context['source'], extension=eid,
                               knowledge=ProposalViews(store, {eid: extension}, d/'extension').bundle([eid]))
                req = d/'extension.json'
                req.write_bytes(canonical(request))
                extended_file = d/'extended.json'
                receipt = invoke('extend-core', original, req, '--core', '-o', extended_file)
                extended = json.loads(extended_file.read_bytes())
                semantic_file = d/'semantic.json'
                invoke('emit-semantic', extended_file, '--core', '-o', semantic_file)
                subject = json.loads(semantic_file.read_bytes())
                theorem = prove(extended, subject, row['original']['name'], row['helper']['name'], general)
                source_call, target_call = theorem['from'], theorem['to']
                theorem['proof'] = {'Trans': dict(middle=source_call, left='Normalize', right={
                    'Trans': dict(middle=target_call, left=theorem['proof'], right='Normalize')})}
                theorem['from'] = subject['functions'][row['original']['name']]
                theorem['to'] = subject['functions'][row['helper']['name']]
                obj = semantic_entry(theorem)
                lid = identity(obj)
                objects = {**parent.bundle([key])['objects'], lid: obj}
                view = ProposalViews(store, objects, d/'law').bundle([lid])
                # Rewrite the shared pure body once, covering callers in both
                # pure and stateful contexts without duplicating an owned call
                # or relying on action-expression extraction exposing it.
                applications = [dict(function=row['original']['name'], path=[], law=lid,
                                     arguments={n: var(s, n) for n, s in theorem['params'].items()},
                                     premises=[])]
                packet = dict(schema=1, semantics='ink-evidence-v1',
                              input_core_sha256=receipt['core_sha256'], knowledge=view,
                              applications=applications)
                yield dict(status='proposal', label='fold-state-projection/'+row['original']['name']+'/'+row['field'],
                           steps=[dict(kind='extension', package=request), dict(kind='rewrite', package=packet)])
            except (ValueError, KeyError, TypeError) as error:
                yield dict(status='declined', label='fold-state-projection/'+row['original']['name'], reason=str(error))
