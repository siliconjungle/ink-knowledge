#!/usr/bin/env python3
"""Re-author current representation examples using an explicitly supplied compiler.

This is an external research producer. Publication follows independent checking;
legacy experiments and measurement snapshots retain their original identities.
"""
import argparse, hashlib, json, os, subprocess, sys, tempfile
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store
from ink_knowledge.store import canonical, read
from ink_knowledge.implementation_candidates import identity_selection, publish_candidates
from producers.representations import generate
from producers.representation_bridge import generate as bridge
from producers.action_replacement import produce
from producers.packed_representations import generate as packed


def refresh(compiler, distribution):
    compiler, distribution = compiler.resolve(), distribution.resolve()
    knowledge = Path(__file__).resolve().parents[1]
    os.environ['INK_COMPILER'] = str(compiler)
    requests, migrations, sources, layouts = {}, {}, {}, {}
    with tempfile.TemporaryDirectory(prefix='ink-research-republication-') as temporary:
        scratch = Path(temporary)
        def run(*args):
            result = subprocess.run([str(compiler), *map(str, args)], capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError(result.stderr)
            return result.stdout
        def write(path, value):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(canonical(value) + b'\n')
        def model(source, label):
            path = scratch / (label + '.json')
            run('emit-action-model', source, '-o', path)
            return read(path)
        def propose(group, source, labels, migration, **options):
            original = model(source, group)
            proposal = generate(original, scratch / (group + '-database'), **options)
            for label, request in zip(labels, proposal['requests']):
                path = knowledge / 'research' / group / (label + '.json')
                test = scratch / group / (label + '.json')
                write(test, request)
                run('check-representation', source, test)
                requests[path] = request
                sources[path] = source
            if migration:
                migrations[knowledge / 'research' / group / (migration + '.json')] = (
                    knowledge / 'research' / group / (labels[0] + '.json'),
                    knowledge / 'research' / group / (labels[1] + '.json'), proposal['migration'])
            print('checked', group, labels, flush=True)
            return proposal
        def connect(group, label, before, after, via_logical=False):
            a, b = knowledge / 'research' / before, knowledge / 'research' / after
            result = bridge(requests[a], requests[b], scratch / (label + '-bridge'), via_logical)
            migrations[knowledge / 'research' / group / (label + '.json')] = (a, b, result)

        source = distribution / 'examples/point-query-delta.ink'
        propose('point-delta', source, ['direct', 'delta'], 'migration', cache_query='zero', preserve_cache=True, delta_query=True)
        propose('point-delta', source, ['direct', 'refresh'], None, cache_query='zero', preserve_cache=True)
        connect('point-delta', 'forward', 'point-delta/refresh.json', 'point-delta/delta.json')
        connect('point-delta', 'reverse', 'point-delta/refresh.json', 'point-delta/direct.json', True)
        source = knowledge / 'research/source-representations/app.ink'
        propose('source-representations', source, ['direct', 'reversed-query-cache'], 'migration', cache_query='zero', retain_queries=False)
        propose('source-representations', source, ['retained-direct', 'retained-query-cache'], 'retained-migration', cache_query='zero')

        source = knowledge / 'research/cache-maintenance/app.ink'
        propose('cache-maintenance', source, ['direct', 'refresh'], None, cache_query='zero')
        propose('cache-maintenance', source, ['direct', 'preserve'], 'migration', cache_query='zero', preserve_cache=True)
        original = model(source, 'replacement-original')
        selected = scratch / 'selected.ink'
        old = 'Rows.remove(key); Rows.remove(key);'
        assert source.read_text().count(old) == 1
        selected.write_text(source.read_text().replace(old, 'Rows.remove(key);'))
        modified = model(selected, 'replacement-selected')
        core = scratch / 'selected-core.json'
        run('emit-core', selected, '-o', core)
        replacement = produce(original, modified, read(core), scratch / 'replacement-database', knowledge)
        replacement['selected_model'] = modified
        propose('cache-maintenance', source, ['composed-direct', 'composed'], 'composed-migration', cache_query='zero', preserve_cache=True, replacement=replacement)
        propose('compact-queries', source, ['direct', 'cached'], 'migration', cache_query='zero', preserve_cache=True, compact_queries=True, replacement=replacement)
        previous = knowledge / 'research/compact-queries/previous.json'
        requests[previous] = requests[knowledge / 'research/cache-maintenance/composed.json']
        sources[previous] = source
        connect('layout-switch', 'forward', 'compact-queries/previous.json', 'compact-queries/cached.json')
        connect('layout-switch', 'backward', 'compact-queries/cached.json', 'compact-queries/previous.json')
        source = knowledge / 'research/keep-parity/app.ink'
        propose('keep-parity', source, ['representation-0', 'representation-1'], 'migration', cache_query='zero', preserve_cache=True, compact_queries=True, delta_query=True)
        source = distribution / 'examples/filtered-aggregate.ink'
        propose('filtered-aggregate', source, ['direct', 'refresh'], None, cache_query='total_query', preserve_cache=True)
        propose('filtered-aggregate', source, ['direct', 'sum-delta'], 'sum-forward', cache_query='total_query', preserve_cache=True, aggregate_query=True)
        propose('filtered-aggregate', source, ['direct', 'count-delta'], 'count-forward', cache_query='count_query', preserve_cache=True, aggregate_query=True)
        source = knowledge / 'research/storage-bulk/app.ink'
        propose('storage-bulk', source, ['direct'], None)
        original = model(source, 'packed-source')
        for label, width, hot_keys in [('packed-2', 2, ()), ('packed-4', 4, ()),
                                      ('indexed-2-hot-0', 2, (0,)), ('indexed-4-hot-0', 4, (0,)),
                                      ('indexed-4-hot-1023', 4, (1023,))]:
            proposal = packed(original, scratch / (label + '-database'), width, hot_keys, compiler)
            request = proposal['request']
            path = knowledge / 'research/storage-bulk' / (label + '.json')
            test = scratch / (label + '.json')
            write(test, request)
            run('check-representation', source, test)
            requests[path], sources[path], layouts[label] = request, source, proposal['layouts']
            print('checked storage-bulk', label, flush=True)
        source = knowledge / 'research/storage-bulk/booleans.ink'
        propose('storage-bulk', source, ['boolean-direct', 'any-delta'], None,
                cache_query='any_query', preserve_cache=True, aggregate_query=True)
        propose('storage-bulk', source, ['boolean-direct', 'all-delta'], None,
                cache_query='all_query', preserve_cache=True, aggregate_query=True)
        for path, (a, b, result) in migrations.items():
            test = scratch / 'bridge-check.json'
            before, after = scratch / 'before.json', scratch / 'after.json'
            write(test, result); write(before, requests[a]); write(after, requests[b])
            run('check-migration', sources[a], before, after, test)
            print('checked bridge', path.parent.name, path.stem, flush=True)

        # Append immutable objects and move discovery names; retain every old snapshot.
        existing = Store(knowledge)
        objects = {i: existing.object(i) for i in existing.members()}
        names = read(existing.data / 'names.json')
        for path, request in requests.items():
            objects.update(request['knowledge']['objects'])
            names[str(path.relative_to(knowledge / 'research')).removesuffix('.json')] = request['representation']
        for path, (_, _, result) in migrations.items():
            objects.update(result['knowledge']['objects'])
            names[str(path.relative_to(knowledge / 'research')).removesuffix('.json')] = result['root']
        published = Store.publish(knowledge, objects.values(), names)
        published.rebuild()
        for path, request in requests.items():
            request = {**request, 'knowledge': published.bundle([request['representation']])}
            write(path, request)
        for path, (_, _, result) in migrations.items():
            write(path, {**result, 'knowledge': published.bundle([result['root']])})
        write(knowledge / 'research/storage-bulk/layouts.json', layouts)
        request = read(knowledge / 'research/point-delta/delta.json')
        root = knowledge / 'research/implementation-candidates'
        candidates, ids = publish_candidates(root, [identity_selection(request['input_core_sha256']), request])
        write(root / 'candidates.json', ids[1:])
        write(root / 'publication.json', dict(source=request['input_core_sha256'], snapshot=candidates.snapshot_id, baseline=ids[0], candidates=ids[1:]))
        receipt = dict(schema=1, compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                       snapshot=published.snapshot_id, checked_representations=len(requests), checked_bridges=len(migrations),
                       scope='Re-authored and universally checked current examples; historical measurements retain their original packages.')
        write(knowledge / 'research/representation-republication.json', receipt)
        print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--distribution', type=Path, required=True)
    args = parser.parse_args()
    refresh(args.compiler, args.distribution)
