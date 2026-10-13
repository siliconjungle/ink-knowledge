"""Untrusted plan-time instances of laws stated over algebraic structure.

A structure law is a published general law (`ink-general-laws-v1`) with type
parameters and quantified assumptions about its function parameters, such as
"the accumulator has an absorbing state" or "two steps commute". It is proved
once. This producer finds program sites matching its left side, binds the law's
types and function parameters by ordinary higher-order pattern matching, and
enumerates a few small witnesses for parameters the program does not mention
(an absorbing constant, say). For each candidate it builds a concrete law whose
proof is `Use` of the general law with one proof per assumption, then keeps it
only if the compiler's `knowledge-check` admits it against the actual module.

Matching, witness choice and proof strategies are search heuristics. The
kernel checks every assumption for the concrete step; a heuristic can only lose
an instance, never admit a false one.
"""
import copy
import json
import subprocess
import tempfile
import time
from pathlib import Path

from .store import semantic_entry, identity, canonical

GENERAL = 'ink-general-laws-v1'
WORDS = {'U8', 'U16', 'U32', 'U64', 'I8', 'I16', 'I32', 'I64'}
MAX_LAWS = 256
MAX_SITES = 64
MAX_WITNESS_COMBINATIONS = 8
MAX_CHECKS = 64
MAX_SECONDS = 20.0


def rename_types(value, names):
    """Mark a general law's type parameters as template variables for matching."""
    if isinstance(value, dict):
        if set(value) == {'Named'} and value['Named'] in names:
            return {'Named': '$' + value['Named']}
        return {k: rename_types(v, names) for k, v in value.items()}
    if isinstance(value, list):
        return [rename_types(v, names) for v in value]
    return value


def operations(term, out):
    node = term.get('node') if isinstance(term, dict) else None
    if isinstance(node, dict):
        if 'Op' in node:
            out.add(node['Op'][0])
            for child in node['Op'][1]:
                operations(child, out)
        elif 'Lambda' in node:
            operations(node['Lambda'], out)
        elif 'Cons' in node:
            for child in node['Cons']:
                operations(child, out)
    return out


def closed(term, depth=0):
    from ink_planner.semantic_search import children
    node = term['node']
    if isinstance(node, dict) and 'Bound' in node and node['Bound'] >= depth:
        return False
    return all(closed(c, depth + int(isinstance(node, dict) and 'Lambda' in node)) for c in children(term))


def free_variables(term, out):
    from ink_planner.semantic_search import children
    node = term['node']
    if isinstance(node, dict) and 'Free' in node:
        if node['Free'] in out and out[node['Free']] != term['sort']:
            raise ValueError('free variable sort conflict')
        out[node['Free']] = term['sort']
    for child in children(term):
        free_variables(child, out)
    return out


def literals(term, sort, out):
    from ink_planner.semantic_search import children
    node = term['node']
    if term.get('sort') == sort and isinstance(node, dict) and len(node) == 1:
        kind = next(iter(node))
        if kind in ('Word', 'Bool', 'Int') and term not in out:
            out.append(copy.deepcopy(term))
    for child in children(term):
        literals(child, sort, out)
    return out


def constants(sort, site):
    """Small witness candidates of a value sort: canonical and site literals."""
    value = sort.get('Value') if isinstance(sort, dict) else None
    found = []
    if value == 'Bool':
        found = [dict(sort=sort, node={'Bool': False}), dict(sort=sort, node={'Bool': True})]
    elif isinstance(value, str) and value in WORDS:
        found = [dict(sort=sort, node={'Word': 0})]
    for item in literals(site, sort, []):
        if item not in found:
            found.append(item)
    return found[:4]


def witnesses(sort, site):
    """Candidates for a parameter the matched site does not determine."""
    if isinstance(sort, dict) and 'Arrow' in sort:
        argument, result = sort['Arrow']
        if result == {'Value': 'Bool'} and isinstance(argument, dict) and 'Value' in argument:
            out = []
            for c in constants(argument, site):
                body = dict(sort={'Value': 'Bool'}, node={'Op': ['binary:==', [dict(sort=argument, node={'Bound': 0}), c]]})
                out.append(dict(sort=sort, node={'Lambda': body}))
            return out
        return []
    return constants(sort, site)


def equality_witness(term):
    """`apply(fn(s) => s == c, x)` gives (x, c); anything else gives None."""
    node = term.get('node')
    if not (isinstance(node, dict) and node.get('Op', [None])[0] == 'apply'):
        return None
    function, argument = node['Op'][1]
    body = function['node'].get('Lambda') if isinstance(function['node'], dict) else None
    if body is None or not isinstance(body['node'], dict) or body['node'].get('Op', [None])[0] != 'binary:==':
        return None
    left, right = body['node']['Op'][1]
    if left['node'] != {'Bound': 0} or not closed(right):
        return None
    return argument, right


def substitute_bound(term, depth, value):
    """Replace bound index `depth` by `value`, lowering indices above it."""
    from ink_planner.semantic_search import shift
    node = term['node']
    if isinstance(node, dict) and 'Bound' in node:
        index = node['Bound']
        if index == depth:
            return shift(value, depth)
        if index > depth:
            return dict(sort=term['sort'], node={'Bound': index - 1})
        return term
    if isinstance(node, dict) and 'Op' in node:
        return dict(sort=term['sort'], node={'Op': [node['Op'][0], [substitute_bound(c, depth, value) for c in node['Op'][1]]]})
    if isinstance(node, dict) and 'Lambda' in node:
        return dict(sort=term['sort'], node={'Lambda': substitute_bound(node['Lambda'], depth + 1, value)})
    if isinstance(node, dict) and 'Cons' in node:
        return dict(sort=term['sort'], node={'Cons': [substitute_bound(c, depth, value) for c in node['Cons']]})
    return term


def beta(term, budget=None):
    """Reduce `apply(fn => body, x)` redexes so step bodies become visible.

    Only a search heuristic for choosing case splits; the kernel normalises
    independently when it checks the resulting proof.
    """
    budget = budget if budget is not None else [20_000]
    budget[0] -= 1
    if budget[0] < 0:
        raise ValueError('beta reduction budget')
    node = term['node']
    if isinstance(node, dict) and 'Op' in node:
        args = [beta(c, budget) for c in node['Op'][1]]
        if node['Op'][0] == 'apply' and len(args) == 2 and isinstance(args[0]['node'], dict) and 'Lambda' in args[0]['node']:
            return beta(substitute_bound(args[0]['node']['Lambda'], 0, args[1]), budget)
        return dict(sort=term['sort'], node={'Op': [node['Op'][0], args]})
    if isinstance(node, dict) and 'Lambda' in node:
        return dict(sort=term['sort'], node={'Lambda': beta(node['Lambda'], budget)})
    if isinstance(node, dict) and 'Cons' in node:
        return dict(sort=term['sort'], node={'Cons': [beta(c, budget) for c in node['Cons']]})
    return term


def choose_conditions(term, out):
    from ink_planner.semantic_search import children
    node = term['node']
    if isinstance(node, dict) and node.get('Op', [None])[0] == 'call:choose':
        condition = node['Op'][1][0]
        if closed(condition) and condition not in out:
            out.append(condition)
    for child in children(term):
        choose_conditions(child, out)
    return out


COMPARISONS = {'binary:<', 'binary:<=', 'binary:>', 'binary:>=', 'binary:==', 'binary:!='}
ORDERED = {'U32', 'U64', 'I32', 'Int'}


def order_atoms(term, out):
    """Closed operands of comparisons, looking through `choose` results.

    `a > choose(b > s, b, s)` gives a, b and s: once the inner comparison is
    decided the outer one compares atoms. Only a heuristic for the kernel's
    order analysis, which decides every comparison among the atoms itself.
    """
    from ink_planner.semantic_search import children

    def operand(t):
        node = t['node']
        if isinstance(node, dict) and node.get('Op', [None])[0] == 'call:choose':
            for branch in node['Op'][1][1:]:
                operand(branch)
        elif closed(t) and t not in out:
            out.append(t)

    node = term['node']
    if isinstance(node, dict) and node.get('Op', [None])[0] in COMPARISONS:
        left, right = node['Op'][1]
        if isinstance(left.get('sort'), dict) and left['sort'].get('Value') in ORDERED:
            operand(left)
            operand(right)
    for child in children(term):
        order_atoms(child, out)
    return out


def assumption_strategies(assumption, arguments, environment):
    """Candidate kernel proofs for one assumption of one concrete instance."""
    from ink_planner.semantic_search import substitute
    rename = dict(arguments)
    for name, sort in assumption.get('params', {}).items():
        fresh = '__assumed_' + name
        if fresh in environment:
            return ['Normalize']
        rename[name] = dict(sort=sort, node={'Free': fresh})
    conditions = [dict(substitute(c['from'], rename), _to=substitute(c['to'], rename)) for c in assumption.get('conditions', [])]
    goal = [substitute(assumption['from'], rename), substitute(assumption['to'], rename)]
    strategies = ['Normalize']
    for index, condition in enumerate(conditions):
        found = equality_witness({k: v for k, v in condition.items() if k != '_to'})
        if found is not None and condition['_to']['node'] == {'Bool': True}:
            subject, value = found
            premise = {'Trans': dict(middle={k: v for k, v in condition.items() if k != '_to'}, left='Normalize', right={'Hypothesis': index})}
            strategies.append({'AssertEquality': dict(equality={'from': subject, 'to': value}, premise=premise, body='Normalize')})
    cases = []
    atoms = []
    try:
        for side in goal:
            reduced = beta(side)
            choose_conditions(reduced, cases)
            order_atoms(reduced, atoms)
    except ValueError:
        cases = atoms = []
    # Split on atomic conditions first: nested ones usually reduce to them.
    atomic = [c for c in cases if not choose_conditions(c, [])]
    cases = (atomic + [c for c in cases if c not in atomic])[:3]
    if cases:
        proof = 'Normalize'
        for condition in reversed(cases):
            proof = {'Cases': dict(condition=condition, on_false=proof, on_true=proof)}
        strategies.append(proof)
    # Comparisons among a few same-sorted atoms (maxima, minima, clamps,
    # threshold steps) need transitivity, which case splits cannot supply.
    sorts = {json.dumps(a['sort'], sort_keys=True) for a in atoms}
    if 2 <= len(atoms) <= 5 and len(sorts) == 1:
        strategies.append({'Order': dict(atoms=atoms, body='Normalize')})
    return strategies


def general_laws(store, subject_operations):
    after = None
    found = {}
    while True:
        page = store.query(kind='rewrite', semantics=GENERAL, after=after, limit=256)
        for ident in page:
            obj = store.object(ident)
            payload = obj['payload']
            if not payload.get('assumptions') or payload.get('conditions'):
                continue
            needed = operations(payload['from'], set()) - {'apply'}
            if needed <= subject_operations:
                found[ident] = obj
            if len(found) >= MAX_LAWS:
                return found
        if len(page) < 256:
            return found
        after = page[-1]


class Checker:
    """Bounded compiler admission of candidate instances against the module."""

    def __init__(self, compiler, core, store, directory):
        self.compiler, self.store, self.directory = compiler, store, Path(directory)
        self.core = self.directory / 'core.json'
        self.core.write_bytes(canonical(core) + b'\n')
        self.checks = 0
        self.started = time.monotonic()

    def admits(self, ident, obj):
        from .proposal_views import ProposalViews
        if self.checks >= MAX_CHECKS or time.monotonic() - self.started > MAX_SECONDS:
            raise TimeoutError('structure instance check budget')
        self.checks += 1
        view_dir = self.directory / f'view-{self.checks}'
        try:
            closure = {ident: obj}
            pending = list(obj['dependencies'])
            while pending:
                dep = pending.pop()
                if dep in closure:
                    continue
                closure[dep] = self.store.object(dep)
                pending.extend(closure[dep]['dependencies'])
                if len(closure) > 4096:
                    return False
            view = ProposalViews(self.store, closure, view_dir).bundle([ident])
        except (ValueError, KeyError):
            return False
        path = self.directory / f'view-{self.checks}.json'
        path.write_bytes(canonical(view) + b'\n')
        result = subprocess.run([str(self.compiler), 'knowledge-check', str(self.core), str(path)],
                                capture_output=True, text=True, timeout=60)
        return result.returncode == 0


def generate(store, subject, core, compiler):
    """Return (objects, receipt) of kernel-admitted concrete structure instances."""
    from ink_planner.semantic_search import substitute, positions
    from .higher_patterns import match as higher_match
    from .law_templates import substitute_types
    from .template_matching import TemplateSites
    from .proposals import nominal_types
    from producers.definition_context28 import bind
    receipt = dict(module='ink_knowledge.structure_instances', laws=0, sites=0, candidates=0, checks=0,
                   admitted=0, skipped=[], scope='Untrusted proposals; each instance was admitted by knowledge-check')
    if compiler is None:
        receipt['skipped'].append('no compiler for instance admission')
        return {}, receipt
    subject_operations = set()
    for body in subject['functions'].values():
        operations(body, subject_operations)
    laws = general_laws(store, subject_operations)
    receipt['laws'] = len(laws)
    if not laws:
        return {}, receipt
    sites = TemplateSites(subject)
    objects = {}
    seen = set()
    with tempfile.TemporaryDirectory(prefix='ink-structure-instances-') as temporary:
        checker = Checker(compiler, core, store, temporary)
        try:
            for law_id, obj in sorted(laws.items()):
                payload = obj['payload']
                names = list(payload.get('types', []))
                pattern = rename_types(payload['from'], names)
                params = rename_types(payload['params'], names)
                matched = 0
                for _, _, target, bindings in sites.matches(pattern, params, names):
                    if matched >= MAX_SITES or not closed(target):
                        continue
                    arguments = {}
                    if not higher_match(pattern, target, params, names, dict(bindings), arguments):
                        continue
                    matched += 1
                    receipt['sites'] += 1
                    typed = substitute_types(dict(params=params, to=rename_types(payload['to'], names),
                                                  frm=pattern, assumptions=rename_types(payload['assumptions'], names)), bindings)
                    missing = [p for p in typed['params'] if p not in arguments]
                    choices = [[]]
                    for name in missing:
                        options = witnesses(typed['params'][name], target)
                        choices = [prefix + [(name, w)] for prefix in choices for w in options][:MAX_WITNESS_COMBINATIONS]
                    for choice in choices:
                        if len(choice) != len(missing):
                            continue
                        complete = dict(arguments, **dict(choice))
                        environment = free_variables(target, {})
                        try:
                            for value in complete.values():
                                free_variables(value, environment)
                        except ValueError:
                            continue
                        to = substitute(typed['to'], complete)
                        middle = substitute(typed['frm'], complete)
                        types = {name: bindings[name] for name in names}
                        per_assumption = [assumption_strategies(a, complete, environment) for a in typed['assumptions']]
                        plans = [[s[0] for s in per_assumption]]
                        widest = max((len(s) for s in per_assumption), default=1)
                        for pick in [-1] + list(range(1, widest)):
                            plan = [s[pick] if len(s) > 1 else s[0] for s in per_assumption]
                            if plan not in plans:
                                plans.append(plan)
                        for proofs in plans:
                            use = dict(law=law_id, arguments=dict(sorted(complete.items())), premises=[],
                                       types=types, assumptions=proofs)
                            candidate = dict(schema=1, semantics=GENERAL, params=dict(sorted(environment.items())),
                                             conditions=[], **{'from': target, 'to': to},
                                             proof={'Trans': dict(middle=middle, left='Normalize', right={'Use': use})},
                                             dependencies=[law_id])
                            if nominal_types(candidate):
                                candidate = bind(candidate, core, subject)
                            entry = semantic_entry(candidate)
                            ident = identity(entry)
                            if ident in seen:
                                break
                            seen.add(ident)
                            receipt['candidates'] += 1
                            if checker.admits(ident, entry):
                                objects[ident] = entry
                                receipt['admitted'] += 1
                                break
        except TimeoutError as error:
            receipt['skipped'].append(str(error))
        receipt['checks'] = checker.checks
    return objects, receipt
