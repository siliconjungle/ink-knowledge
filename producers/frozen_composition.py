#!/usr/bin/env python3
"""Propose typed helper chunks and replay a complete immutable-state plan.

An explicit compile-time proposal, not automatic profitable selection. Helper
admission changes no existing definition; complete transition proofs authorize
the action rewrite. Failed construction/checking never publishes an output.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, identity
from ink_knowledge.store import entry, MAX_VIEW_BYTES
from producers.action_replacement import alpha_normal, call, cons, convert, var
from producers.fold_chunks import FoldChunks, compose
from producers.frozen_specialization import Partial, substitute, source_free
from producers.point_delta import free_variables, lift, normal, replace, sub

EXTENSION_BATCH_SIZE = 256


class ChunkPartial(Partial):
    def __init__(self, program, *, share_helpers=True, owned_chunk_width=1, closed_call=None):
        super().__init__(program, closed_call=closed_call)
        if owned_chunk_width not in (1, 2, 4, 8):
            raise ValueError('owned chunk width must be 1, 2, 4 or 8')
        self.owned_chunk_width = owned_chunk_width
        self.share_helpers = share_helpers
        self.helpers = []
        self.helper_index = {}
        self.helper_names = set()

    def should_inline(self, name, args, original):
        if name in self.helper_names:
            return all(self.value(x) for x in args)
        # Bound this proposal to newly known call arguments. Expanding an
        # already literal initializer merely duplicates unchanged library code
        # in every caller, increasing source/proof cost without new facts.
        return any(self.value(a) and not self.value(b) for a,b in zip(args,original))

    def intern(self, function):
        """Share generated code, never results or evaluations.

        The key records exact types, free/callee names, literals and operand
        order. Only parameter and lexical binder spelling is discarded. This
        is an untrusted proposal; source extension and action equality replay
        still decide admission independently of the key.
        """
        if not self.share_helpers:
            if len(self.helpers) >= FoldChunks.MAX_HELPERS:
                raise ValueError('frozen composition helper budget')
            self.helpers.append(function)
            self.helper_names.add(function['name']);self.functions[function['name']]=function
            return function['name']
        serial = 0
        def binder():
            nonlocal serial
            name = serial; serial += 1; return name
        bindings = {name: binder() for name, _ in function['params']}
        def visit(value, env, depth=0):
            self.tick(depth)
            if isinstance(value, list):
                return [visit(v, env, depth+1) for v in value]
            if not isinstance(value, dict):
                return value
            if 'Var' in value:
                name = value['Var']
                return {'bound': env[name]} if name in env else {'free': name}
            if 'Lambda' in value:
                name, body = value['Lambda']; local = binder()
                return {'Lambda': [local, visit(body, {**env, name: local}, depth+1)]}
            if 'Let' in value:
                name, ty, initial, body = value['Let']; local = binder()
                return {'Let': [local, ty, visit(initial, env, depth+1),
                    visit(body, {**env, name: local}, depth+1)]}
            return {key: visit(v, env, depth+1) for key, v in value.items()}
        key = json.dumps([[ty for _, ty in function['params']], function['result'],
                          visit(function['body'], bindings)], sort_keys=True, separators=(',', ':'))
        if key not in self.helper_index:
            if len(self.helpers) >= FoldChunks.MAX_HELPERS:
                raise ValueError('frozen composition helper budget')
            self.helper_index[key] = function['name']
            self.helpers.append(function)
            self.helper_names.add(function['name']);self.functions[function['name']]=function
        return self.helper_index[key]

    def inline_call(self, function, args, active, depth):
        names = [self.fresh() for _ in args]
        for name, (_, ty) in zip(names, function['params']):
            self.types[name] = ty
        body = substitute(function['body'], {p[0]: {'Var': name} for p, name in zip(function['params'], names)})
        closed = {name: value for name, value in zip(names, args) if self.value(value)}
        body = self.expr(body, closed, active, depth+1)
        dynamic = [(name, ty, value) for name, (_, ty), value in zip(names, function['params'], args) if name not in closed]
        def traversal(value):
            if isinstance(value, list):
                return any(traversal(v) for v in value)
            if not isinstance(value, dict):
                return False
            return (value.get('Call', [None])[0] in ('foldl', 'foldr', 'repeat', 'repeat_until')
                    or any(traversal(v) for v in value.values()))
        def owned_work(value):
            if isinstance(value, list):
                return any(owned_work(v) for v in value)
            if not isinstance(value, dict):
                return False
            ty = self.known_type(value)
            return ((ty is not None and not self.plain(ty))
                    or any(owned_work(v) for v in value.values()))
        # Actions have capability typing; temporary affine storage belongs in
        # pure functions. Keep an outer pure boundary around owned work after
        # its traversal disappears, while allowing nested steps to specialize
        # inside that boundary. Source checking still rejects invalid transfers.
        if traversal(body) or (len(active) == 1 and owned_work(body)):
            # A residual pure traversal stays behind a typed function boundary.
            # Dynamic arguments retain their original order, including unused
            # arguments. The conservative extension and complete action proof
            # still establish legality; this is no cached equality verdict.
            helper = self.intern(dict(name=self.fresh(),params=[[n,t] for n,t,_ in dynamic],
                                      result=function['result'],body=body))
            return {'Call': [helper,[value for _,_,value in dynamic]]}
        for name, ty, value in reversed(dynamic):
            body = {'Let': [name,ty,value,body]}
        return self.preserve_result(body, function['result'])

    def plain(self, ty, active=()):
        if isinstance(ty, str):
            return ty in ('U32', 'U64', 'I32', 'F32', 'Int', 'Bool', 'Unit', 'String')
        if isinstance(ty, dict) and 'Named' in ty:
            name = ty['Named']
            return name in self.program['enums'] or name in self.program['ids'] or (name not in active and name in self.program['records']
                and all(self.plain(t, (*active, name)) for _, t in self.program['records'][name]))
        if isinstance(ty, dict):
            for container in ['List', 'Option']:
                if container in ty:
                    return self.plain(ty[container], active)
            if 'Result' in ty:
                return all(self.plain(t, active) for t in ty['Result'])
            if 'Vector' in ty:
                return self.plain(ty['Vector'][0], active)
        return False

    def known_type(self, value):
        inherited = super().known_type(value)
        if inherited is not None:
            return inherited
        if not isinstance(value, dict):
            return 'Unit' if value == 'Unit' else None
        if 'Var' in value:
            return self.types.get(value['Var'])
        for key, ty in [('Float', 'F32'), ('Bool', 'Bool'), ('String', 'String')]:
            if key in value:
                return ty
        if 'Record' in value:
            return {'Named': value['Record'][0]}
        if 'Call' in value and value['Call'][0] in self.functions:
            return self.functions[value['Call'][0]]['result']
        if value.get('Call', [None])[0] == 'buffer' and len(value['Call'][1]) == 1:
            source = self.known_type(value['Call'][1][0])
            if isinstance(source, dict) and 'List' in source:
                return {'Buffer': source['List']}
        return None

    def threaded(self, ty, active=()):
        """Types passed once from one chunk to the next, never captured twice.

        This only bounds proposal construction. The source checker must still
        admit the generated linear calls and the kernel must prove the complete
        action equation. Captures retain the stricter immutable ``plain`` gate.
        """
        if self.plain(ty, active):
            return True
        if not isinstance(ty, dict):
            return False
        if 'Named' in ty:
            name = ty['Named']
            return (name not in active and name in self.program['records']
                    and all(self.threaded(t, (*active, name))
                            for _, t in self.program['records'][name]))
        for container in ['Buffer', 'List', 'Option']:
            if container in ty:
                return self.threaded(ty[container], active)
        if 'Map' in ty:
            return all(self.threaded(t, active) for t in ty['Map'])
        if 'Result' in ty:
            return all(self.threaded(t, active) for t in ty['Result'])
        if 'Vector' in ty:
            return self.threaded(ty['Vector'][0], active)
        return False

    def fold(self, name, args, active, depth):
        if name != 'foldl' or len(args) != 3:
            return super().fold(name, args, active, depth)
        rows, initial, callback = args
        if (not isinstance(rows, dict) or rows.get('Call', [None])[0] != 'list'
                or not self.value(rows) or len(rows['Call'][1]) <= FoldChunks.MAX_CHUNK
                or not isinstance(callback, dict) or 'Lambda' not in callback):
            return super().fold(name, args, active, depth)
        element, inner = callback['Lambda']
        if not isinstance(inner, dict) or 'Lambda' not in inner:
            return super().fold(name, args, active, depth)
        accumulator, body = inner['Lambda']; result = self.known_type(initial)
        captures = sorted(source_free(body, {element, accumulator}) - self.enums
                          - self.program['enums'].keys() - {'None'})
        if (result is None or not self.threaded(result)
                or any(n not in self.types or not self.plain(self.types[n]) for n in captures)):
            return super().fold(name, args, active, depth)
        values = rows['Call'][1]
        # Owned record fields can reuse an earlier primal several times. Keep
        # their leaf equations smaller, within the same checker work/depth
        # bounds; balanced composition retains scalability without expanding
        # the full owned computation into one proof term.
        width = FoldChunks.MAX_CHUNK if self.plain(result) else min(self.owned_chunk_width, FoldChunks.MAX_CHUNK)
        count = (len(values) + width - 1) // width
        if 2*count-1 > FoldChunks.MAX_HELPERS:
            raise ValueError('frozen composition helper budget')
        names = [self.fresh() for _ in range(count)]
        capture_params = [[n, self.types[n]] for n in captures]
        for index, name in enumerate(names):
            initial_name = self.fresh(); previous = initial_name; self.types[previous] = result
            params = capture_params + [[initial_name, result]]
            bindings = []
            for value in values[index*width:(index+1)*width]:
                self.tick(depth)
                following = self.fresh(); self.types[following] = result
                expression = self.expr(body, {element: value, accumulator: {'Var': previous}},
                                       active, depth + 1)
                bindings.append((following, expression)); previous = following
            expression = {'Var': previous}
            for local, value in reversed(bindings):
                expression = {'Let': [local, result, value, expression]}
            names[index] = self.intern(dict(name=name, params=params, result=result, body=expression))
        # A balanced composition tree bounds source/checker/host call depth by
        # log(chunk count), instead of putting every chunk on one call stack.
        while len(names) > 1:
            level = []
            for offset in range(0, len(names), 2):
                if offset+1 == len(names):
                    level.append(names[offset]); continue
                name, argument, middle = self.fresh(), self.fresh(), self.fresh()
                arguments = [*[{'Var': n} for n in captures], {'Var': argument}]
                expression = {'Let': [middle, result, {'Call': [names[offset], arguments]},
                    {'Call': [names[offset+1], [*[{'Var': n} for n in captures], {'Var': middle}]]}]}
                level.append(self.intern(dict(name=name, params=capture_params+[[argument,result]],
                                              result=result, body=expression)))
            names = level
        arguments = [*[{'Var': n} for n in captures],initial]
        invocation = {'Call':[names[0],arguments]}
        # Only a completely closed invocation can collapse. Dynamic primals
        # retain their balanced helper graph and original arithmetic order.
        return self.expr(invocation,{},active,depth+1) if all(self.value(a) for a in arguments) else invocation


def propose_source(source, *, share_helpers=True, owned_chunk_width=1, closed_call=None):
    selected = copy.deepcopy(source); partial = ChunkPartial(selected['program'], share_helpers=share_helpers,
                                                           owned_chunk_width=owned_chunk_width, closed_call=closed_call)
    for action in selected['program']['actions']:
        partial.types = dict(action['params'])
        # Optional expansion is transactional per complete action. A large
        # training action must not discard already constructed serving code.
        # Work remains charged; exhaustion never raises an existing limit.
        names = ['serial','generated','contextual','types','functions','helpers',
                 'helper_index','helper_names','keep_values']
        snapshot = {key: copy.copy(getattr(partial,key)) for key in names}
        try:
            body = partial.statements(action['body'], {n: {'Var': n} for n, _ in action['params']})
        except ValueError as error:
            if str(error) not in ('frozen composition helper budget', 'frozen specialization work budget'):
                raise
            for key, saved in snapshot.items():
                setattr(partial,key,saved)
        else:
            action['body'] = body
    selected['program']['functions'].extend(partial.helpers)
    return selected, partial.helpers


def witness_helpers(selected, helpers):
    """Only unreachable plain helpers need an auxiliary query for projection.

    Reachable helpers are already projected through complete actions. Owned
    signatures cannot cross an action interface; their surviving pure calls
    stay behind ordinary source ownership checking. This is an authoring choice,
    never proof admission or a semantic reachability certificate.
    """
    program = selected['program']
    functions = {f['name']: f for f in program['functions']}
    pending = [a['body'] for a in program['actions']]
    reached = set()
    work = 0
    while pending:
        work += 1
        if work > FoldChunks.MAX_WORK:
            raise ValueError('frozen witness reachability work budget')
        value = pending.pop()
        if isinstance(value, list):
            pending.extend(value)
        elif isinstance(value, dict):
            if 'Call' in value:
                name = value['Call'][0]
                if name in functions and name not in reached:
                    reached.add(name)
                    pending.append(functions[name]['body'])
            pending.extend(value.values())
    partial = ChunkPartial(program)
    return [f for f in helpers if f['name'] not in reached and partial.plain(f['result'])
            and all(partial.plain(t) for _, t in f['params'])]


def comparison_chunks(before_objects, after_objects, witness_objects=None, *, owned_chunk_width=1, pure_helpers=None):
    """Prepare untrusted universal fold bridges for source correspondence."""
    objects = {**(witness_objects or {}), **before_objects, **after_objects}
    helpers = set()
    for key, obj in objects.items():
        function = obj['payload'].get('declaration', {}).get('Function')
        if (key not in before_objects and function and function['params']
                and (key in pure_helpers if pure_helpers is not None else function['params'][0][0] == 'pure_arg_0')):
            helpers.add(key)
    chunks = FoldChunks(objects, helpers, owned_chunk_width=owned_chunk_width)
    recursive = {key for key,obj in objects.items() if obj['payload'].get('declaration',{}).get('Function',{}).get('recursive') is not None}
    direct = {}
    initial_helpers = set(helpers)
    def raw_dependencies(helper):
        pending = [helper]; seen = set(); result = set()
        while pending:
            chunks.tick(); key = pending.pop()
            if key in seen: continue
            seen.add(key)
            if key not in direct:
                direct[key] = chunks.references(objects[key]['payload']['declaration']['Function']['body'])
            for dependency in direct[key]:
                if dependency in initial_helpers or dependency in chunks.folds:
                    result.add(dependency)
                elif dependency not in recursive and dependency not in chunks.closed:
                    if 'Function' in objects[dependency]['payload'].get('declaration',{}):
                        pending.append(dependency)
        return result
    raw = {key:raw_dependencies(key) for key in helpers}
    while True:
        # A residual workload fold needs its own induction bridge. Ordinary
        # recursive value operations (such as logical Buffer.push) can remain
        # opaque on both sides of a chunk equation; recursion alone does not
        # disqualify an otherwise straight-line source helper.
        # A dependency walk can accept the common case without expanding local
        # owner binds. If it finds a possible residual fold, retain the existing
        # normalization attempt so dead branches can still disappear.
        possible = {key for key in helpers if raw[key] & (chunks.folds.keys()|(initial_helpers-helpers))}
        rejected = {key for key in possible if chunks.references(normal(objects[key]['payload']['declaration']['Function']['body'],objects,
            opaque=helpers|chunks.closed,blocked=recursive,heads=chunks.closed)) & (chunks.folds.keys()|(chunks.helpers-helpers))}
        if not rejected:break
        helpers-=rejected
    chunks.helpers=helpers
    # Keep owner boundaries during complete-action exposure. Open them with
    # universal case lemmas at the comparison site, not by normalizing an
    # entire concrete graph inside a frame's state/event context.
    chunks.gates = {key for key in recursive if key not in helpers
                    and key not in chunks.folds and chunks.acyclic(key)}
    return chunks


def produce(before, after, selected, directory, witnesses=None, *, owned_chunk_width=1):
    if (before['semantics'] not in ('ink-action-transition-v1', 'ink-action-transition-v2') or after['semantics'] != before['semantics']
            or not before.get('frozen_domain') or before['frozen_domain'] != after.get('frozen_domain')
            or before['state'] != after['state'] or before['events'] != after['events']):
        raise ValueError('frozen composition projection/domain mismatch')
    pure_helpers = None
    if before['semantics'] == 'ink-action-transition-v2':
        pure_helpers = {f['function'] for model in [after, witnesses or {}]
                        for f in model.get('pure_functions', {}).values()}
    chunks = comparison_chunks(before['objects'], after['objects'],
        (witnesses or {}).get('objects'), owned_chunk_width=owned_chunk_width, pure_helpers=pure_helpers)
    helpers = chunks.helpers
    objects = {**(witnesses or {}).get('objects', {}), **before['objects'], **after['objects']}
    fixed = [chunks.share(e['to']) for e in before['frozen_domain']]
    opaque = helpers | chunks.closed | chunks.gates
    proofs = {}
    equality = None
    for name, old in before['actions'].items():
        new = after['actions'][name]; args = [var(n) for n, _ in old['params']]
        old_call, new_call = call(old['function'], args), call(new['function'], args)
        if old['function'] == new['function']:
            proofs[name] = {'Refl': old_call}; continue
        state = cons(before['state'], 0, [var(n) for n in old['case']['bindings']])
        def expose(action):
            term = normal(action['case']['call'], chunks.objects, opaque=opaque, blocked=chunks.folds,heads=chunks.closed)
            steps = [convert(action['case']['call'], term)]
            for index, equation in enumerate(before['frozen_domain']):
                left = sub(equation['from'], {'initial': state}); right, lemma = fixed[index]
                exposed = normal(left, chunks.objects)
                context = replace(term, exposed, var('composition_fact_hole'))
                if context == term:
                    continue
                equality = compose([{'Sym': convert(left, exposed)}, {'Hypothesis': index},
                    {'Use': dict(theorem=lemma, arguments=[], premises=[])}])
                steps.append(lift(equality, context, 'composition_fact_hole'))
                term = replace(term, exposed, right)
            normalized = alpha_normal(normal(term, chunks.objects, opaque=opaque, blocked=chunks.folds,heads=chunks.closed))
            steps.append(convert(term, normalized))
            return normalized, compose(steps)
        left, forward = expose(old); right, backward = expose(new)
        def align(a, z):
            if a == z:
                return a, []
            chunks.tick()
            if (isinstance(a, dict) and isinstance(z, dict) and 'Call' in a and 'Call' in z
                    and a['Call']['function'] in chunks.folds and z['Call']['function'] in helpers):
                lemma, arguments = chunks.bridge_application(a['Call'],z['Call'])
                return z, [{'Use': dict(theorem=lemma, arguments=arguments, premises=[])}]
            if (isinstance(a,dict) and 'Call' in a and a['Call']['function'] in chunks.folds
                    and not free_variables(a) and not free_variables(z)):
                return z,[chunks.closed_application(a['Call'],z)]
            raise ValueError('frozen composition has unmatched source structure')
        # Locate whole term opportunities, then lift once through the complete
        # transition context, avoiding congruence over JSON container fragments.
        def pairs(a, z):
            if a == z:
                return []
            if (isinstance(a,dict) and 'Call' in a and a['Call']['function'] in chunks.folds
                    and not free_variables(a) and not free_variables(z)):
                return [(a,z)]
            if isinstance(a, dict) and isinstance(z, dict) and 'Call' in a and 'Call' in z:
                if a['Call']['function'] in chunks.folds and z['Call']['function'] in helpers:
                    return [(a, z)]
            if isinstance(a, dict) and isinstance(z, dict) and a.keys() == z.keys():
                return [pair for key in a for pair in pairs(a[key], z[key])]
            if isinstance(a, list) and isinstance(z, list) and len(a) == len(z):
                return [pair for x, y in zip(a, z) for pair in pairs(x, y)]
            raise ValueError('frozen composition has unmatched source structure')
        current = left; steps = [forward]
        try:
            opportunities = pairs(left, right)
        except ValueError as error:
            if str(error) != 'frozen composition has unmatched source structure':
                raise
            from producers.computation_equality import ComputationEquality
            if equality is None:
                equality = ComputationEquality(chunks)
            fields = chunks.objects[before['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields']
            env = {n:t for n,t in old['params'] if n!='initial'}
            env.update(zip(old['case']['bindings'],fields))
            steps += [equality.prove(left,right,env,len(before['frozen_domain'])), {'Sym': backward}]
        else:
            for a, z in opportunities:
                _, proofs_at_site = align(a, z)
                hole = 'composition_hole'
                context = replace(current, a, var(hole))
                steps.append(lift(compose(proofs_at_site), context, hole)); current = replace(current, a, z)
            steps += [convert(current, right), {'Sym': backward}]
        proof = compose(steps)
        if any(objects[key]['payload']['declaration']['Function']['recursive'] is not None for key in helpers):
            fields = chunks.objects[before['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields']
            env = {n:t for n,t in old['params'] if n!='initial'}
            env.update(zip(old['case']['bindings'],fields))
            proof = chunks.factor_conversions(proof,env)
        proofs[name] = {'Cases': dict(variable='initial', **{'from': old_call, 'to': new_call},
            cases=[dict(bindings=old['case']['bindings'], proof=proof)])}
    # Import the equations actually used by these complete proofs. Search may
    # have built unused intermediate proposals; their presence in an authoring
    # cache is neither admission nor a reason to inflate the checked view.
    roots = {a['function'] for m in [before, after] for a in m['actions'].values()} | chunks.references(proofs)
    # Preserve exact immutable-source definitions even when selected actions
    # stop reading them. Membership is checked independently of theorem truth.
    for equation in before['frozen_domain']:
        roots.update(chunks.references(equation))
    store = Store.publish(directory, list(chunks.objects.values()))
    replacement = dict(selected=selected, proofs=proofs)
    if before['semantics'] == 'ink-action-transition-v2':
        replacement['projection'] = 'structural-v2'
    return dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=before['source'],
        knowledge=store.bundle(sorted(roots)), applications=[], action_replacement=replacement)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path); parser.add_argument('--ink', required=True, type=Path)
    parser.add_argument('-o', '--output', required=True, type=Path)
    parser.add_argument('--projection', choices=['legacy', 'structural-v2'], default='structural-v2',
                        help='explicit source correspondence version, independently re-derived by checking')
    parser.add_argument('--helper-layout', choices=['shared', 'expanded'], default='shared',
                        help='explicit code layout proposal; both layouts require complete proofs')
    parser.add_argument('--owned-chunk-width', type=int, choices=[1, 2, 4, 8], default=1,
                        help='explicit owned-helper leaf size; proof and profitability remain separate')
    args = parser.parse_args()
    if args.source.stat().st_size > 16_000_000:
        raise ValueError('frozen composition source byte limit')
    source = json.loads(args.source.read_bytes())
    from producers.closed_reference_calls import ReferenceCalls
    selected, helpers = propose_source(source, share_helpers=args.helper_layout == 'shared',
                                      owned_chunk_width=args.owned_chunk_width,
                                      closed_call=ReferenceCalls(args.source, args.ink))
    if not helpers:
        raise ValueError('no admitted closed traversal chunk opportunity')
    with tempfile.TemporaryDirectory(prefix='ink-frozen-composition-') as folder:
        folder = Path(folder)
        def run(*command):
            result = subprocess.run([str(args.ink.resolve()), *map(str, command)], capture_output=True)
            result.check_returncode()
        def model(core, name):
            path = folder/(name+'.json'); run('emit-action-model', core, '--core', '--projection', args.projection, '-o', path)
            return json.loads(path.read_bytes())
        original = model(args.source, 'original')
        plan = dict(schema=1, semantics='ink-compiled-plan-v1', input_core_sha256=original['source'],
                    steps=[])
        packet = folder/'plan.json'; state = folder/'state.json'; current=original['source']
        # Compose the existing bounded extension contract. Each batch binds
        # its exact checked predecessor; no larger trusted admission is needed
        # merely because smaller leaves require more helper declarations.
        for start in range(0,len(helpers),EXTENSION_BATCH_SIZE):
            obj=entry('definition','ink-source-extension-v1',dict(functions=helpers[start:start+EXTENSION_BATCH_SIZE]))
            key=identity(obj);store=Store.publish(folder/('extensions-'+str(start)),[obj])
            request=dict(schema=1,semantics='ink-source-extension-v1',input_core_sha256=current,
                         knowledge=store.bundle([key]),extension=key)
            plan['steps'].append(dict(kind='extension',package=request))
            packet.write_text(json.dumps(plan,separators=(',',':')))
            run('check-plan',args.source,packet,'--core','--state-out',state)
            checked=json.loads(state.read_bytes());current=checked['source']
        extended = folder/'extended.json'; extended.write_text(json.dumps(checked['core']))
        candidate = folder/'selected.json'; candidate.write_text(json.dumps(selected))
        # A completely evaluated helper is absent from the selected actions'
        # reachable projection. Project it through an auxiliary pure query so
        # its ordinary mathematical definition can witness the closed fold.
        # These queries are never added to either executable or selected source.
        witness_source = copy.deepcopy(selected)
        occupied = {a['name'] for a in witness_source['program']['actions']}
        occupied.update(f['name'] for f in witness_source['program']['functions'])
        for index, helper in enumerate(witness_helpers(selected, helpers)):
            name = 'frozen_proof_witness_'+str(index)
            while name in occupied: name += '_'
            occupied.add(name)
            witness_source['program']['actions'].append(dict(name=name,kind='Query',
                params=helper['params'],result=helper['result'],reads=[],writes=[],emits=[],
                body=[{'Return':{'Call':[helper['name'],[{'Var':n} for n,_ in helper['params']]]}}]))
        witness_path = folder/'witnesses.json';witness_path.write_text(json.dumps(witness_source))
        rewrite = produce(model(extended, 'before'), model(candidate, 'after'), selected, folder/'proofs',
                          model(witness_path,'witness-model'), owned_chunk_width=args.owned_chunk_width)
        plan['steps'].append(dict(kind='rewrite', package=rewrite))
        encoded = json.dumps(plan, separators=(',', ':'))+'\n'
        if len(encoded.encode()) > MAX_VIEW_BYTES:
            raise ValueError('frozen composition plan byte budget')
        packet.write_text(encoded); run('check-plan', args.source, packet, '--core')
        args.output.parent.mkdir(parents=True, exist_ok=True)
        pending = None
        try:
            with tempfile.NamedTemporaryFile(prefix='.ink-frozen-plan-', dir=args.output.parent,
                                             delete=False) as output:
                pending = Path(output.name)
                output.write(packet.read_bytes()); output.flush(); os.fsync(output.fileno())
            os.replace(pending, args.output); pending = None
        finally:
            if pending is not None:
                pending.unlink(missing_ok=True)
    print(json.dumps(dict(status='checked-proposal', helpers=len(helpers), steps=len(plan['steps']),
        profitability='unmeasured; explicit selection only')))


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.stderr.decode(errors='replace').strip() or 'compiler rejected frozen composition')
