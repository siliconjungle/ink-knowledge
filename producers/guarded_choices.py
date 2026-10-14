"""Author guarded alternatives from ordinary whole-function equalities.

Recipe data chooses producers and cutoffs. A Cases proof preserves the original
expression on the other branch; neither a cutoff nor recipe provenance grants
equality or profitability. Normal plan admission and measurements remain required.
"""
import copy
import itertools
import json
import tempfile
from importlib.resources import files
from pathlib import Path

from ink_knowledge import Store, identity, semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from producers.semantic_laws import op, value, var, word


def choice_rule(store=None, ident=None):
    """Recipe-selected theorem bytes; every use still replays in the kernel."""
    if ident is not None:
        if store is None:
            raise ValueError('a selected guard theorem needs a pinned store')
        return store.object(ident)
    return json.loads(files('ink_knowledge').joinpath('guarded-choice-law.json').read_bytes())


def guard_entry(ident, entry, condition, equivalence=None):
    """Wrap a concrete equality, retaining its conditions and their authority."""
    if identity(entry) != ident or entry.get('kind') != 'rewrite':
        raise ValueError('guard requires an authentic rewrite object')
    law = entry['payload']
    if any(law.get(k) for k in ('types', 'assumptions')):
        raise ValueError('instantiate general parameters and assumptions before guarding')
    if condition.get('sort') != value('Bool'):
        raise ValueError('guard must have Boolean sort')
    rule = choice_rule() if equivalence is None else equivalence
    rule_id = identity(rule)
    selected = copy.deepcopy(law['to'])
    proof = {'Use': dict(law=rule_id, types={'A': selected['sort']['Value']},
        arguments={'a': law['from'], 'b': selected, 'p': condition},
        premises=[{'Use': dict(law=ident, arguments={n: var(s, n) for n, s in law['params'].items()},
                              premises=[{'Hypothesis': i} for i in range(len(law.get('conditions', [])))])}])}
    authored = dict(schema=1, semantics='ink-general-laws-v1', **copy.deepcopy(law))
    authored.update(to=op(selected['sort'], 'call:choose', condition, selected, copy.deepcopy(law['from'])),
                    proof=proof, dependencies=[ident, rule_id])
    return semantic_entry(authored)


def list_guard(name, sort, cutoff):
    if type(cutoff) is not int or not 1 <= cutoff <= 1_000_000_000:
        raise ValueError('guard cutoff budget')
    if not isinstance(sort, dict) or set(sort) != {'Value'} or not isinstance(sort['Value'], dict) or set(sort['Value']) != {'List'}:
        raise ValueError('size guard requires a List parameter')
    # count has exact Int semantics; do not narrow or wrap the list length.
    return op(value('Bool'), 'binary:>=', op(value('Int'), 'call:count', var(sort, name)), word('Int', cutoff))


def has_size_guard(term):
    """Bound repeated authoring, not proof applicability."""
    if isinstance(term, dict):
        node = term.get('node', {})
        operator = node.get('Op') if isinstance(node, dict) else None
        if operator and operator[0] == 'call:choose':
            condition = operator[1][0].get('node', {})
            comparison = condition.get('Op') if isinstance(condition, dict) else None
            if comparison and comparison[0] == 'binary:>=':
                left = comparison[1][0].get('node', {})
                if isinstance(left, dict) and left.get('Op', [None])[0] == 'call:count':
                    return True
        return any(has_size_guard(v) for v in term.values())
    return isinstance(term, list) and any(has_size_guard(v) for v in term)


def guarded_rows(row, store, directory, cutoff, equivalence=None):
    """Preserve source-extension prefixes and guard one whole-function rewrite."""
    steps = row.get('steps', [row['step']] if 'step' in row else [])
    if row.get('status') != 'proposal' or not steps or steps[-1].get('kind') != 'rewrite':
        return
    if any(s.get('kind') != 'extension' for s in steps[:-1]):
        return
    packet = steps[-1]['package']
    applications = packet['applications']
    if len(applications) != 1 or applications[0]['path']:
        return
    application = applications[0]
    ident = application['law']
    rule = choice_rule() if equivalence is None else equivalence
    objects = {**packet['knowledge']['objects'], identity(rule): rule}
    entry = objects[ident]
    if has_size_guard(entry['payload']['from']):
        return
    views = ProposalViews(store, objects, directory)
    for name, sort in sorted(entry['payload']['params'].items()):
        if not isinstance(sort, dict) or not isinstance(sort.get('Value'), dict) or 'List' not in sort['Value']:
            continue
        obj = guard_entry(ident, entry, list_guard(name, sort, cutoff), rule)
        new = identity(obj)
        views.update({new: obj})
        result = copy.deepcopy(row)
        result.pop('step', None)
        result['steps'] = copy.deepcopy(steps)
        result['label'] = row['label'] + '/guard-count-' + name + '-' + str(cutoff)
        replacement = result['steps'][-1]['package']
        replacement['knowledge'] = views.bundle([new])
        replacement['applications'][0]['law'] = new
        yield result


def propose(context, base_recipes, cutoff, limit=2, equivalence=None):
    """Compose installed, snapshot-bound producers using bounded recipe data."""
    from ink_knowledge.recipes import execute, load
    if type(limit) is not int or not 1 <= limit <= 16:
        raise ValueError('guard candidate budget')
    list_guard('budget', value({'List': 'U32'}), cutoff)
    if not isinstance(base_recipes, list) or not 1 <= len(base_recipes) <= 8 or any(not isinstance(n, str) for n in base_recipes):
        raise ValueError('guard base recipe budget')
    if context.get('_guarded_choice_active'):
        raise ValueError('recursive guarded recipe')
    root = Path(context['knowledge_root'])
    snapshot = root / 'store/snapshots' / (context['knowledge_snapshot'] + '.json')
    store = Store(root, snapshot)
    rule = choice_rule(store, equivalence)
    registry, _ = load(store=store)
    recipes = {r['id']: r for r in registry['recipes']}
    selected = [recipes[name] for name in base_recipes]
    if any(r['module'] == __name__ for r in selected):
        raise ValueError('recursive guarded recipe')
    used = 0
    with tempfile.TemporaryDirectory(prefix='ink-guarded-choices-') as temporary:
        for recipe in selected:
            stream = execute(recipe, dict(context, _guarded_choice_active=True))
            try:
                for index, row in enumerate(itertools.islice(stream, 16)):
                    try:
                        directory = Path(temporary) / identity(recipe) / str(index)
                        for result in guarded_rows(row, store, directory, cutoff, rule):
                            yield result
                            used += 1
                            if used >= limit:
                                return
                    except (ValueError, KeyError, TypeError) as error:
                        yield dict(status='declined', label='guarded/' + recipe['id'], reason=str(error))
            finally:
                stream.close()
