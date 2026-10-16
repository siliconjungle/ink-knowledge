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
from ink_knowledge.store import entry
from producers.action_replacement import alpha_normal, call, cons, convert, var
from producers.fold_chunks import FoldChunks, compose
from producers.frozen_specialization import Partial, substitute
from producers.point_delta import lift, normal, replace, sub


def source_free(value, bound=frozenset()):
    if isinstance(value, list):
        return set().union(*(source_free(x, bound) for x in value)) if value else set()
    if not isinstance(value, dict):
        return set()
    if 'Var' in value:
        return {value['Var']} - bound
    if 'Lambda' in value:
        name, body = value['Lambda']; return source_free(body, bound | {name})
    if 'Let' in value:
        name, _, initial, body = value['Let']
        return source_free(initial, bound) | source_free(body, bound | {name})
    return set().union(*(source_free(x, bound) for x in value.values()))


class ChunkPartial(Partial):
    def __init__(self, program):
        super().__init__(program)
        self.helpers = []

    def plain(self, ty, active=()):
        if isinstance(ty, str):
            return ty in ('U32', 'U64', 'I32', 'F32', 'Int', 'Bool', 'Unit', 'String')
        if isinstance(ty, dict) and 'Named' in ty:
            name = ty['Named']
            return name in self.program['enums'] or (name not in active and name in self.program['records']
                and all(self.plain(t, (*active, name)) for _, t in self.program['records'][name]))
        if isinstance(ty, dict) and any(k in ty for k in ('List', 'Option', 'Result', 'Vector')):
            return all(self.plain(t, active) for t in (ty.get('Result') or [ty.get('List', ty.get('Option', ty.get('Vector', [None])[0]))]))
        return False

    def known_type(self, value):
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
        return None

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
        if (result is None or not self.plain(result)
                or any(n not in self.types or not self.plain(self.types[n]) for n in captures)):
            return super().fold(name, args, active, depth)
        values = rows['Call'][1]
        count = (len(values) + FoldChunks.MAX_CHUNK - 1) // FoldChunks.MAX_CHUNK
        if len(self.helpers) + count > FoldChunks.MAX_HELPERS:
            raise ValueError('frozen composition helper budget')
        if len(self.helpers) + 2*count-1 > FoldChunks.MAX_HELPERS:
            raise ValueError('frozen composition helper budget')
        names = [self.fresh() for _ in range(count)]
        capture_params = [[n, self.types[n]] for n in captures]
        for index, name in enumerate(names):
            initial_name = self.fresh(); previous = initial_name; self.types[previous] = result
            params = capture_params + [[initial_name, result]]
            bindings = []
            for value in values[index*FoldChunks.MAX_CHUNK:(index+1)*FoldChunks.MAX_CHUNK]:
                self.tick(depth)
                following = self.fresh(); self.types[following] = result
                expression = self.expr(substitute(body, {element: value, accumulator: {'Var': previous}}),
                                       {}, active, depth + 1)
                bindings.append((following, expression)); previous = following
            expression = {'Var': previous}
            for local, value in reversed(bindings):
                expression = {'Let': [local, result, value, expression]}
            self.helpers.append(dict(name=name, params=params, result=result, body=expression))
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
                self.helpers.append(dict(name=name, params=capture_params+[[argument,result]],
                                         result=result, body=expression))
                level.append(name)
            names = level
        return {'Call': [names[0], [*[{'Var': n} for n in captures], initial]]}


def propose_source(source):
    selected = copy.deepcopy(source); partial = ChunkPartial(selected['program'])
    for action in selected['program']['actions']:
        partial.types = dict(action['params'])
        action['body'] = partial.statements(action['body'])
    selected['program']['functions'].extend(partial.helpers)
    return selected, partial.helpers


def produce(before, after, selected, directory):
    if (before['semantics'] != 'ink-action-transition-v1' or after['semantics'] != before['semantics']
            or not before.get('frozen_domain') or before['frozen_domain'] != after.get('frozen_domain')
            or before['state'] != after['state'] or before['events'] != after['events']):
        raise ValueError('frozen composition projection/domain mismatch')
    objects = {**before['objects'], **after['objects']}
    helpers = set()
    for key, obj in after['objects'].items():
        function = obj['payload'].get('declaration', {}).get('Function')
        if (key not in before['objects'] and function and function['params']
                and function['params'][0][0] == 'pure_arg_0'):
            helpers.add(key)
    chunks = FoldChunks(objects, helpers)
    fixed = [chunks.share(e['to']) for e in before['frozen_domain']]
    opaque = helpers | chunks.closed
    proofs = {}
    for name, old in before['actions'].items():
        new = after['actions'][name]; args = [var(n) for n, _ in old['params']]
        old_call, new_call = call(old['function'], args), call(new['function'], args)
        if old['function'] == new['function']:
            proofs[name] = {'Refl': old_call}; continue
        state = cons(before['state'], 0, [var(n) for n in old['case']['bindings']])
        def expose(action):
            term = normal(action['case']['call'], chunks.objects, opaque=opaque, blocked=chunks.folds)
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
            normalized = alpha_normal(normal(term, chunks.objects, opaque=opaque, blocked=chunks.folds))
            steps.append(convert(term, normalized))
            return normalized, compose(steps)
        left, forward = expose(old); right, backward = expose(new)
        def align(a, z):
            if a == z:
                return a, []
            chunks.tick()
            if (isinstance(a, dict) and isinstance(z, dict) and 'Call' in a and 'Call' in z
                    and a['Call']['function'] in chunks.folds and z['Call']['function'] in helpers):
                invocation = a['Call']; target = z['Call']; dynamic = invocation['arguments'][1:]
                if dynamic != target['arguments']:
                    raise ValueError('frozen composition dynamic argument correspondence')
                lemma = chunks.bridge(invocation['function'], invocation['arguments'][0], target['function'])
                return z, [{'Use': dict(theorem=lemma, arguments=dynamic, premises=[])}]
            raise ValueError('frozen composition has unmatched source structure')
        # Locate whole term opportunities, then lift once through the complete
        # transition context, avoiding congruence over JSON container fragments.
        def pairs(a, z):
            if a == z:
                return []
            if isinstance(a, dict) and isinstance(z, dict) and 'Call' in a and 'Call' in z:
                if a['Call']['function'] in chunks.folds and z['Call']['function'] in helpers:
                    return [(a, z)]
            if isinstance(a, dict) and isinstance(z, dict) and a.keys() == z.keys():
                return [pair for key in a for pair in pairs(a[key], z[key])]
            if isinstance(a, list) and isinstance(z, list) and len(a) == len(z):
                return [pair for x, y in zip(a, z) for pair in pairs(x, y)]
            raise ValueError('frozen composition has unmatched source structure')
        current = left; steps = [forward]
        for a, z in pairs(left, right):
            _, proofs_at_site = align(a, z)
            hole = 'composition_hole'
            context = replace(current, a, var(hole))
            steps.append(lift(compose(proofs_at_site), context, hole)); current = replace(current, a, z)
        steps += [convert(current, right), {'Sym': backward}]
        proofs[name] = {'Cases': dict(variable='initial', **{'from': old_call, 'to': new_call},
            cases=[dict(bindings=old['case']['bindings'], proof=compose(steps))])}
    roots = {a['function'] for m in [before, after] for a in m['actions'].values()} | chunks.lemmas
    # Preserve exact immutable-source definitions even when selected actions
    # stop reading them. Membership is checked independently of theorem truth.
    for equation in before['frozen_domain']:
        roots.update(chunks.references(equation))
    store = Store.publish(directory, list(chunks.objects.values()))
    return dict(schema=1, semantics='ink-evidence-v1', input_core_sha256=before['source'],
        knowledge=store.bundle(sorted(roots)), applications=[],
        action_replacement=dict(selected=selected, proofs=proofs))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path); parser.add_argument('--ink', required=True, type=Path)
    parser.add_argument('-o', '--output', required=True, type=Path); args = parser.parse_args()
    if args.source.stat().st_size > 16_000_000:
        raise ValueError('frozen composition source byte limit')
    source = json.loads(args.source.read_bytes()); selected, helpers = propose_source(source)
    if not helpers:
        raise ValueError('no admitted closed traversal chunk opportunity')
    with tempfile.TemporaryDirectory(prefix='ink-frozen-composition-') as folder:
        folder = Path(folder)
        def run(*command):
            result = subprocess.run([str(args.ink.resolve()), *map(str, command)], capture_output=True)
            result.check_returncode()
        def model(core, name):
            path = folder/(name+'.json'); run('emit-action-model', core, '--core', '-o', path)
            return json.loads(path.read_bytes())
        original = model(args.source, 'original')
        obj = entry('definition', 'ink-source-extension-v1', dict(functions=helpers)); key = identity(obj)
        store = Store.publish(folder/'extensions', [obj])
        request = dict(schema=1, semantics='ink-source-extension-v1', input_core_sha256=original['source'],
            knowledge=store.bundle([key]), extension=key)
        plan = dict(schema=1, semantics='ink-compiled-plan-v1', input_core_sha256=original['source'],
                    steps=[dict(kind='extension', package=request)])
        packet = folder/'plan.json'; packet.write_text(json.dumps(plan, separators=(',', ':')))
        state = folder/'state.json'; run('check-plan', args.source, packet, '--core', '--state-out', state)
        extended = folder/'extended.json'; extended.write_text(json.dumps(json.loads(state.read_bytes())['core']))
        candidate = folder/'selected.json'; candidate.write_text(json.dumps(selected))
        rewrite = produce(model(extended, 'before'), model(candidate, 'after'), selected, folder/'proofs')
        plan['steps'].append(dict(kind='rewrite', package=rewrite))
        encoded = json.dumps(plan, separators=(',', ':'))+'\n'
        if len(encoded.encode()) > 16_000_000:
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
    print(json.dumps(dict(status='checked-proposal', helpers=len(helpers), steps=2,
        profitability='unmeasured; explicit selection only')))


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.stderr.decode(errors='replace').strip() or 'compiler rejected frozen composition')
