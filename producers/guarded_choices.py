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
    """Bound repeated authoring, including conjunctions of size conditions."""
    def count_test(t):
        if isinstance(t,dict):
            operator=t.get('node',{}).get('Op') if isinstance(t.get('node'),dict) else None
            if operator and operator[0]=='binary:>=':
                left=operator[1][0].get('node',{})
                if isinstance(left,dict) and left.get('Op',[None])[0]=='call:count':return True
            return any(count_test(v)for v in t.values())
        return isinstance(t,list) and any(count_test(v)for v in t)
    if isinstance(term,dict):
        node=term.get('node',{});operator=node.get('Op')if isinstance(node,dict)else None
        if operator and operator[0]=='call:choose' and count_test(operator[1][0]):return True
        return any(has_size_guard(v)for v in term.values())
    return isinstance(term,list) and any(has_size_guard(v)for v in term)


def guarded_rows(row, store, directory, cutoff, equivalence=None, joint=False, subject=None, core=None):
    """Guard independent root equalities; preserve extensions and premises.

    Joint mode guards every eligible function with the conjunction of its List
    parameter bounds. Given the exact source subject, repeated/local steps first
    become ordinary whole-body proof proposals and still require full replay.
    """
    steps=row.get('steps',[row['step']]if 'step'in row else [])
    if row.get('status')!='proposal' or not steps or steps[-1].get('kind')!='rewrite':return
    if any(s.get('kind')!='extension'for s in steps[:-1]):return
    packet=steps[-1]['package'];applications=packet['applications']
    if not 1<=len(applications)<=128:return
    complex_steps=any(a['path']for a in applications)or len({a['function']for a in applications})!=len(applications)
    if complex_steps:
        if subject is None or core is None:return
        from producers.selection_composition import compose
        packet=compose(packet,subject,core,store,Path(directory)/'whole-function')
        steps=copy.deepcopy(steps);steps[-1]['package']=packet;applications=packet['applications']
    if not joint and len(applications)!=1:return
    rule=choice_rule()if equivalence is None else equivalence
    objects={**packet['knowledge']['objects'],identity(rule):rule}
    changes=[]
    for index,application in enumerate(applications):
        ident=application['law'];entry=objects[ident]
        if has_size_guard(entry['payload']['from']):return
        conditions=[(name,list_guard(name,sort,cutoff))for name,sort in sorted(entry['payload']['params'].items())
            if isinstance(sort,dict)and isinstance(sort.get('Value'),dict)and 'List'in sort['Value']]
        if joint and conditions:
            condition=conditions[0][1]
            for _,test in conditions[1:]:condition=op(value('Bool'),'binary:&&',condition,test)
            changes.append((index,ident,entry,'+'.join(n for n,_ in conditions),condition))
        elif not joint:
            changes.extend((index,ident,entry,name,condition)for name,condition in conditions)
    if not changes:return
    views=ProposalViews(store,objects,directory)
    variants=[changes]if joint else [[change]for change in changes]
    for variant in variants:
        result=copy.deepcopy(row);result.pop('step',None);result['steps']=copy.deepcopy(steps)
        replacement=result['steps'][-1]['package'];roots=set(packet['knowledge']['roots']);labels=[]
        for index,ident,entry,name,condition in variant:
            obj=guard_entry(ident,entry,condition,rule);new=identity(obj);views.update({new:obj})
            replacement['applications'][index]['law']=new;roots.add(new)
            labels.append(applications[index]['function']+':'+name)
        # Original roots include independent laws used by application premises.
        # Keep them along with every guarded root; the full chain is replayed.
        replacement['knowledge']=views.bundle(sorted(roots))
        result['label']=row['label']+'/guard-count-'+','.join(labels)+'-'+str(cutoff)
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
