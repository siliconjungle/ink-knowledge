"""Untrusted portable context construction for ordinary checked semantic laws.

No optimiser-specific proof rule: callers still supply Normalize/Use/Trans/etc.
Function signatures and exact typed bodies come from the checked semantic subject.
The independent checker validates definitions, identities and the resulting proof.
"""
import copy
from ink_knowledge import canonical, identity


def calls(value, names):
    found = set()

    def walk(v):
        if isinstance(v, dict):
            op = v.get('node', {}).get('Op') if isinstance(v.get('node'), dict) else None
            if op and op[0].startswith('call:') and op[0][5:] in names:
                found.add(op[0][5:])
            for child in v.values():
                walk(child)
        elif isinstance(v, list):
            for child in v:
                walk(child)

    walk(value)
    return found


def capture(core, subject, roots):
    program = core['program']
    functions = {f['name']: f for f in program['functions']}
    definitions = {}
    bodies = {}
    pending = list(sorted(set(roots)))
    while pending:
        name = pending.pop()
        if name in bodies:
            continue
        if len(bodies) >= 128:
            raise ValueError('definition context closure limit')
        if name not in functions or name not in subject['functions']:
            raise ValueError('definition context requires a supported semantic body: '+name)
        function = functions[name]
        body = subject['functions'][name]
        callees = calls(body, functions)
        bodies[name] = dict(params=copy.deepcopy(function['params']), result=function['result'],
                            body=copy.deepcopy(body), callees={n: '' for n in sorted(callees)})
        pending.extend(sorted(callees))

    indices = {}; low = {}; stack = []; active = set(); components = []
    def visit(name):
        indices[name] = low[name] = len(indices)
        stack.append(name); active.add(name)
        for callee in bodies[name]['callees']:
            if callee not in indices:
                visit(callee); low[name] = min(low[name], low[callee])
            elif callee in active:
                low[name] = min(low[name], indices[callee])
        if low[name] == indices[name]:
            members = []
            while True:
                member = stack.pop(); active.remove(member); members.append(member)
                if member == name: break
            components.append(sorted(members))
    for name in sorted(bodies):
        if name not in indices: visit(name)

    groups = {}
    for members in components:
        # Tarjan produces dependencies before their callers.
        for name in members:
            for callee in bodies[name]['callees']:
                if callee not in members:
                    bodies[name]['callees'][callee] = definitions[callee]['sha256']
        cyclic = len(members) > 1 or members[0] in bodies[members[0]]['callees']
        if cyclic:
            payload = {name: copy.deepcopy(bodies[name]) for name in members}
            for definition in payload.values():
                definition['callees'] = {n:i for n,i in definition['callees'].items() if n not in members}
            group = identity(['ink-recursive-definitions-v1', payload])
            groups[group] = members
            for name in members:
                for callee in bodies[name]['callees']:
                    if callee in members: bodies[name]['callees'][callee] = group
        for name in members:
            definitions[name] = dict(sha256=identity(bodies[name]), definition=bodies[name])

    context = dict(schema=1, definitions=dict(sorted(definitions.items())),
                   records=copy.deepcopy(program.get('records', {})),
                   enums=copy.deepcopy(program.get('enums', {})))
    if groups:
        context['recursive_groups'] = dict(sorted(groups.items()))
    if program.get('ids'):
        context['ids']=copy.deepcopy(program['ids'])
    if len(canonical(context)) > 4_000_000:
        raise ValueError('definition context byte limit')
    return context


def bind(law, core, subject, roots=None):
    result = copy.deepcopy(law)
    names = {f['name'] for f in core['program']['functions']}
    if roots is None:
        roots = calls(law, names)
    result['definition_context'] = capture(core, subject, roots)
    return result
