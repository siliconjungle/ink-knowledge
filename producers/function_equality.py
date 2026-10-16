#!/usr/bin/env python3
"""Author unconditional source-bound pure-function equalities.

This is proof search, not admission. All definitions, intermediate theorems and
the complete function replacement replay in core. No profile, frozen-state fact
or sampled agreement supplies a premise.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, canonical
from producers.action_replacement import call, var
from producers.computation_equality import ComputationEquality
from producers.frozen_composition import comparison_chunks
from producers.point_delta import free_variables


class FunctionEquality(ComputationEquality):
    def normalize(self, term, env, depth=0):
        term = super().normalize(term, env, depth)
        def share(value):
            self.chunks.tick()
            if isinstance(value, dict):
                if 'Construct' in value and not free_variables(value):
                    return self.chunks.share_data(value)
                return {key: share(child) for key, child in value.items()}
            if isinstance(value, list):
                return [share(child) for child in value]
            return value
        # Closed source literals remain transparent ordinary definitions. This
        # bounds written proof depth; Convert must still establish each step.
        return share(term)


def produce(before, after, selected, directory, *, owned_chunk_width=4):
    if (before['semantics'] != 'ink-source-functions-v1'
            or after['semantics'] != before['semantics']
            or not before['functions']
            or before['functions'].keys() != after['functions'].keys()):
        raise ValueError('function equality projection mismatch')
    chunks = comparison_chunks(before['objects'], after['objects'],
                               owned_chunk_width=owned_chunk_width)
    equality = FunctionEquality(chunks)
    proofs = {}
    roots = set()
    for name, old in before['functions'].items():
        new = after['functions'][name]
        if old['params'] != new['params'] or old['result'] != new['result']:
            raise ValueError('function equality projected signature mismatch')
        arguments = [var(n) for n, _ in old['params']]
        left, right = call(old['function'], arguments), call(new['function'], arguments)
        proof = equality.prove(left, right, dict(old['params']))
        proofs[name] = chunks.factor_conversions(proof, dict(old['params']))
        roots.update([old['function'], new['function']])
    roots.update(chunks.lemmas)
    store = Store.publish(directory, list(chunks.objects.values()))
    return dict(schema=1, semantics=before['semantics'], input_core_sha256=before['source'],
                selected=selected, knowledge=store.bundle(sorted(roots)), proofs=proofs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('selected', type=Path)
    parser.add_argument('--ink', required=True, type=Path)
    parser.add_argument('-o', '--output', required=True, type=Path)
    parser.add_argument('--owned-chunk-width', type=int, choices=[1, 2, 4, 8], default=4)
    args = parser.parse_args()
    for path in [args.source, args.selected]:
        if path.stat().st_size > 16_000_000:
            raise ValueError('function equality source byte limit')
    source, selected = [json.loads(path.read_bytes()) for path in [args.source, args.selected]]
    old = {f['name']: f for f in source['program']['functions']}
    new = {f['name']: f for f in selected['program']['functions']}
    if old.keys() != new.keys():
        raise ValueError('add helpers in a preceding checked source extension')
    names = sorted(name for name in old if old[name]['body'] != new[name]['body'])
    if not names:
        raise ValueError('function equality requires changed source bodies')
    with tempfile.TemporaryDirectory(prefix='ink-function-equality-') as temporary:
        folder = Path(temporary)
        def run(*command):
            result = subprocess.run([str(args.ink.resolve()), *map(str, command)],
                                    capture_output=True, timeout=180)
            result.check_returncode()
        def model(path, name):
            output = folder/(name+'.json')
            run('emit-function-model', path, '--core', '--functions', ','.join(names), '-o', output)
            return json.loads(output.read_bytes())
        before, after = model(args.source, 'before'), model(args.selected, 'after')
        replacement = produce(before, after, selected, folder/'knowledge',
                              owned_chunk_width=args.owned_chunk_width)
        plan = dict(schema=1, semantics='ink-compiled-plan-v1', input_core_sha256=before['source'],
                    steps=[dict(kind='functions', package=replacement)])
        packet = folder/'plan.json'; packet.write_bytes(canonical(plan))
        run('check-plan', args.source, packet, '--core')
        args.output.parent.mkdir(parents=True, exist_ok=True)
        pending = None
        try:
            with tempfile.NamedTemporaryFile(prefix='.ink-functions-', dir=args.output.parent,
                                             delete=False) as output:
                pending = Path(output.name)
                output.write(packet.read_bytes()); output.flush(); os.fsync(output.fileno())
            os.replace(pending, args.output); pending = None
        finally:
            if pending is not None:
                pending.unlink(missing_ok=True)
    print(json.dumps(dict(status='checked-proposal', functions=names,
                          profitability='unmeasured; explicit selection only')))


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.stderr.decode(errors='replace').strip() or 'compiler rejected function equality')
