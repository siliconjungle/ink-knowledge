"""Propose scalar observation arguments for small immutable-record helpers.

Source discovery and profitability are untrusted. Every new helper is an
ordinary source extension, and replacement requires a source-bound Normalize
equality. No compiler operation, application name or invariant is recognised.
"""
import copy
import json
import subprocess
import tempfile
from pathlib import Path

from ink_knowledge import Store, canonical, entry, identity, semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from producers.definition_context28 import bind
from producers.semantic_laws import law, op, value, var

SCALARS = {'U32', 'U64', 'I32', 'F32', 'Bool'}


def candidates(core, limit=32):
    if limit <= 0: return []
    program = core['program']
    records = program['records']
    functions = {f['name']: f for f in program['functions']}

    def immutable(ty, active=frozenset()):
        if isinstance(ty, str): return True
        if not isinstance(ty, dict): return False
        if 'Named' in ty:
            name = ty['Named']
            return name not in active and name in records and all(
                immutable(t, active | {name}) for _, t in records[name])
        if 'List' in ty: return immutable(ty['List'], active)
        if 'Option' in ty: return immutable(ty['Option'], active)
        if 'Result' in ty: return all(immutable(t, active) for t in ty['Result'])
        return False

    def inferred(expr, env):
        if 'Var' in expr: return env.get(expr['Var'])
        if 'Field' in expr:
            receiver, field = expr['Field']; ty = inferred(receiver, env)
            if isinstance(ty, dict) and 'Named' in ty:
                return dict(records.get(ty['Named'], [])).get(field)
        if 'Call' in expr:
            name, args = expr['Call']
            if name == 'length' and len(args) == 1: return 'U32'
            if name in functions: return functions[name]['result']
        if 'Method' in expr and expr['Method'][1] == 'len': return 'U32'
        return None

    def root(expr):
        if 'Var' in expr: return expr['Var']
        if 'Field' in expr: return root(expr['Field'][0])
        return None

    result = []
    for function in program['functions']:
        if not isinstance(function['result'], str) or function['result'] not in SCALARS: continue
        params = dict(function['params'])
        aggregates = {n for n, t in function['params'] if isinstance(t, dict)
                      and 'Named' in t and immutable(t)}
        if not aggregates or len(canonical(function['body'])) > 8192: continue
        observations, shadowed, remaining = [], set(), set()

        def observation(expr, env, available):
            ty = inferred(expr, env)
            if not isinstance(ty, str) or ty not in SCALARS: return None
            if 'Field' in expr and root(expr) in available:
                return root(expr), ty
            receiver = None
            if 'Call' in expr and expr['Call'][0] == 'length' and len(expr['Call'][1]) == 1:
                receiver = expr['Call'][1][0]
            if 'Method' in expr and expr['Method'][1:] == ['len', []]: receiver = expr['Method'][0]
            receiver_type = inferred(receiver, env) if receiver is not None else None
            if (isinstance(receiver_type, dict) and 'List' in receiver_type
                    and root(receiver) in available):
                return root(receiver), ty
            return None

        def rewrite(expr, env, available):
            found = observation(expr, env, available)
            if found is not None:
                name = next((n for n, _, e, _ in observations if e == expr), None)
                if name is None:
                    name = 'observed_' + str(len(observations))
                    while name in params or name in shadowed: name += '_'
                    observations.append((name, found[1], copy.deepcopy(expr), found[0]))
                return {'Var': name}
            if 'Lambda' in expr: raise ValueError('callback helper outside bounded proposal family')
            if 'Let' in expr:
                name, annotation, initial, body = expr['Let']; shadowed.add(name)
                local = dict(env); local[name] = annotation or inferred(initial, env)
                return {'Let': [name, annotation, rewrite(initial, env, available),
                                rewrite(body, local, available - {name})]}
            if 'Var' in expr and expr['Var'] in available: remaining.add(expr['Var'])
            def descend(v):
                if isinstance(v, dict): return rewrite(v, env, available)
                if isinstance(v, list): return [descend(x) for x in v]
                return copy.deepcopy(v)
            return {k: descend(v) for k, v in expr.items()}

        try: body = rewrite(function['body'], params, aggregates)
        except ValueError: continue
        used = {source for _, _, _, source in observations}
        if not observations or remaining or used != aggregates or len(observations) > 8: continue
        # Fresh argument bindings must not be shadowed by any nested source let.
        if any(name in shadowed for name, _, _, _ in observations): continue
        signature = []
        arguments = []
        for name, ty in function['params']:
            if name not in aggregates:
                signature.append([name, ty]); arguments.append({'Var': name})
            else:
                for observed, ty, expr, source in observations:
                    if source == name:
                        signature.append([observed, ty]); arguments.append(expr)
        helper = dict(name='projected_' + identity(dict(function=function, observations=observations))[:20],
                      params=signature, result=function['result'], body=body)
        if helper['name'] in functions: continue
        result.append(dict(original=function, helper=helper, arguments=arguments))
        if len(result) >= limit: break
    return result


def propose(context, limit=32):
    if context.get('representation'): return
    core = context['core']; rows = candidates(core, limit)
    if not rows: return
    source = context['source']; compiler = context['compiler']
    root = Path(context['knowledge_root'])
    store = Store(root, root / 'store/snapshots' / (context['knowledge_snapshot'] + '.json'))

    def invoke(*args):
        r = subprocess.run([compiler, *map(str, args)], capture_output=True, text=True,
                           timeout=context.get('check_timeout', 120))
        if r.returncode: raise ValueError(r.stderr[-2000:])
        return json.loads(r.stdout) if r.stdout.lstrip().startswith(('{', '[')) else r.stdout

    with tempfile.TemporaryDirectory(prefix='ink-project-arguments-') as temporary:
        directory = Path(temporary); original = directory / 'original.json'
        original.write_bytes(canonical(core))
        definitions = dict(functions=[row['helper'] for row in rows], records={}, enums={}, ids=[])
        extension = entry('definition', 'ink-source-extension-v1', definitions)
        eid = identity(extension)
        request = dict(schema=1, semantics='ink-source-extension-v1', input_core_sha256=source,
                       extension=eid, knowledge=ProposalViews(store, {eid: extension}, directory/'extension').bundle([eid]))
        requestfile = directory/'extension.json'; requestfile.write_bytes(canonical(request))
        extendedfile = directory/'extended.json'
        receipt = invoke('extend-core', original, requestfile, '--core', '-o', extendedfile)
        extended = json.loads(extendedfile.read_bytes())
        semanticfile = directory/'semantic.json'
        invoke('emit-semantic', extendedfile, '--core', '-o', semanticfile)
        subject = json.loads(semanticfile.read_bytes())
        from ink_planner.semantic_search import positions, match
        for row in rows:
            f, helper = row['original'], row['helper']
            env = dict(f['params'])
            def term(expr):
                if 'Var' in expr: return var(value(env[expr['Var']]), expr['Var'])
                if 'Field' in expr:
                    receiver, field = expr['Field']; base = term(receiver)
                    ty = dict(core['program']['records'][base['sort']['Value']['Named']])[field]
                    return op(value(ty), 'field:'+field, base)
                if 'Call' in expr and expr['Call'][0] == 'length':
                    return op(value('U32'), 'call:length', term(expr['Call'][1][0]))
                if 'Method' in expr and expr['Method'][1:] == ['len', []]:
                    return op(value('U32'), 'method:len', term(expr['Method'][0]))
                raise ValueError('unsupported argument observation')
            try:
                left = op(value(f['result']), 'call:'+f['name'], *(var(value(t),n)for n,t in f['params']))
                right = op(value(f['result']), 'call:'+helper['name'], *(term(expr)for expr in row['arguments']))
                theorem = bind(law({n:value(t)for n,t in f['params']},left,right), extended, subject,
                               [f['name'],helper['name']])
                obj = semantic_entry(theorem); lid = identity(obj)
                view = ProposalViews(store, {lid: obj}, directory/'law').bundle([lid])
                applications = []
                for name, body in subject['functions'].items():
                    if name == helper['name']: continue
                    for path, target in positions(body):
                        node = target['node']; call = node.get('Op') if isinstance(node,dict)else None
                        if not call or call[0] != 'call:'+f['name']: continue
                        # Avoid duplicating a computed aggregate expression.
                        # This is a profitability filter, never proof authority.
                        if any(not isinstance(arg['node'],dict)or not set(arg['node'])&{'Free','Bound'}
                               for (param,_),arg in zip(f['params'],call[1])if param in {n for n,t in f['params']if isinstance(t,dict)and 'Named'in t}): continue
                        arguments = {}
                        if match(left,target,theorem['params'],arguments):
                            applications.append(dict(function=name,path=list(path),law=lid,arguments=arguments,premises=[]))
                if not applications: continue
                packet = dict(schema=1,semantics='ink-evidence-v1', input_core_sha256=receipt['core_sha256'],
                              knowledge=view,applications=applications)
                yield dict(status='proposal',label='scalar-observation-arguments/'+f['name'],
                           steps=[dict(kind='extension',package=request),dict(kind='rewrite',package=packet)])
            except (ValueError,KeyError,TypeError) as error:
                yield dict(status='declined',label='scalar-observation-arguments/'+f['name'],reason=str(error))
