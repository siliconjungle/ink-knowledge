#!/usr/bin/env python3
"""Publish the structure law library: general laws checked once by the kernel.

Instances are never published here. `ink_knowledge.structure_instances`
proposes them per program at planning time, and the compiler checks each one.
"""
import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge.store import Store, read

LIBRARY = Path(__file__).resolve().parents[1] / 'libraries' / 'structure-laws.ink'
GENERAL = 'ink-general-laws-v1'
SORTABLE = ('U32', 'U64', 'I32')


def permutation_laws():
    """Fold insensitivity to sorting, for any step whose applications commute.

    Source law syntax cannot name sorted insertion, so these two general laws
    are written in the kernel's JSON form; the kernel still checks both proofs.
    The assumption is exactly what a permutation needs: swapping two adjacent
    steps leaves the accumulator unchanged. Sums, counts, products, minima and
    maxima satisfy it; order-sensitive steps such as list building do not.
    """
    from producers.semantic_laws import value, arrow, var, op
    rows = []
    m = value({'Named': 'M'})
    for element in SORTABLE:
        w, ls = value(element), value({'List': element})
        step_sort = arrow(w, arrow(m, m))
        step = var(step_sort, 'step')
        z = var(m, 'z')
        def apply(f, x, acc):
            return op(m, 'apply', op(arrow(m, m), 'apply', f, x), acc)
        def fold(xs):
            return op(m, 'call:foldr', xs, z, step)
        a, b, t = var(w, 'a'), var(w, 'b'), var(m, 's')
        swaps = dict(name='swaps', params={'a': w, 'b': w, 's': m},
                     **{'from': apply(step, a, apply(step, b, t)), 'to': apply(step, b, apply(step, a, t))})
        x, ys = var(w, 'x'), var(ls, 'ys')
        head, tail = var(w, 'head'), var(ls, 'tail')
        insert = lambda item, items: op(ls, 'list.insert', item, items)
        # insert_fold: foldr(insert(x, ys)) == step(x, foldr(ys)).
        swapped = apply(step, head, apply(step, x, fold(tail)))
        lemma_step = {'Cases': dict(
            condition=op(value('Bool'), 'binary:<=', x, head), on_true='Normalize',
            on_false={'Trans': dict(middle=swapped, left='Normalize', right={'Trans': dict(
                middle=apply(step, x, apply(step, head, fold(tail))),
                left={'Assume': dict(index=0, arguments={'a': head, 'b': x, 's': fold(tail)})},
                right='Normalize')})})}
        lemma = dict(schema=1, semantics=GENERAL, params={'step': step_sort, 'x': w, 'ys': ls, 'z': m},
                     conditions=[], **{'from': fold(insert(x, ys)), 'to': apply(step, x, fold(ys))},
                     proof={'Induction': dict(variable='ys', names=['head', 'tail'], base='Normalize', step=lemma_step)},
                     dependencies=[], types=['M'], assumptions=[swaps])
        from ink_knowledge.store import semantic_entry, identity
        lemma_id = identity(semantic_entry(lemma))
        xs = var(ls, 'xs')
        sorted_tail = op(ls, 'method:sort', tail)
        fresh = {k: var(sort, '__assumed_' + k) for k, sort in swaps['params'].items()}
        use = {'Use': dict(law=lemma_id, arguments={'step': step, 'x': head, 'ys': sorted_tail, 'z': z}, premises=[],
                           types={'M': {'Named': 'M'}}, assumptions=[{'Assume': dict(index=0, arguments=fresh)}])}
        main_step = {'Trans': dict(middle=fold(insert(head, sorted_tail)), left='Normalize', right={'Trans': dict(
            middle=apply(step, head, fold(sorted_tail)), left=use, right='Normalize')})}
        main = dict(schema=1, semantics=GENERAL, params={'step': step_sort, 'xs': ls, 'z': m},
                    conditions=[], **{'from': fold(op(ls, 'method:sort', xs)), 'to': fold(xs)},
                    proof={'Induction': dict(variable='xs', names=['head', 'tail'], base='Normalize', step=main_step)},
                    dependencies=[lemma_id], types=['M'], assumptions=[swaps])
        rows.append((f'insert_fold_{element.lower()}', lemma))
        rows.append((f'fold_sort_{element.lower()}', main))
    return rows


def publish(compiler, root, source=LIBRARY):
    root = Path(root)
    with tempfile.TemporaryDirectory(prefix='ink-structure-laws-') as directory:
        bundle_path = Path(directory) / 'bundle.json'
        completed = subprocess.run([str(compiler), 'emit-laws', str(source), '-o', str(bundle_path)],
                                   capture_output=True, text=True, timeout=120)
        if completed.returncode:
            raise ValueError('structure law authoring rejected: ' + completed.stderr.strip())
        receipt = json.loads(completed.stdout)
        bundle = json.loads(bundle_path.read_text())
    from ink_knowledge.store import semantic_entry, identity
    objects = dict(bundle['objects'])
    published = dict(receipt['names'])
    for name, law in permutation_laws():
        entry = semantic_entry(law)
        objects[identity(entry)] = entry
        published[name] = identity(entry)
    check(compiler, objects, sorted(published.values()))
    store = Store(root)
    names = read(root / 'store' / 'names.json') if (root / 'store' / 'names.json').exists() else {}
    names = dict(names, **{'structure-laws/' + name: ident for name, ident in published.items()})
    store = store.extend(objects.values(), names)
    store.ensure_index()
    return dict(laws=sorted(published), snapshot=store.snapshot_id)


def check(compiler, objects, roots):
    """Kernel-check every library law before publication, against a trivial module."""
    from ink_knowledge.store import canonical
    from ink_knowledge.proposal_views import ProposalViews
    with tempfile.TemporaryDirectory(prefix='ink-structure-check-') as directory:
        d = Path(directory)
        source = d / 'empty.ink'; source.write_text('module structure_check;\nfn unit(x:u32)->u32{return x;}\n')
        core = d / 'core.json'
        subprocess.run([str(compiler), 'emit-core', str(source), '-o', str(core)], check=True, capture_output=True)
        empty = Store.publish(d / 'empty', [])
        view = ProposalViews(empty, objects, d / 'view').bundle(roots)
        path = d / 'view.json'; path.write_bytes(canonical(view) + b'\n')
        completed = subprocess.run([str(compiler), 'knowledge-check', str(core), str(path)], capture_output=True, text=True)
        if completed.returncode:
            raise ValueError('structure law rejected by the kernel: ' + completed.stderr.strip()[-2000:])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    print(json.dumps(publish(args.compiler, args.root)))
