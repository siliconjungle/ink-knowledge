#!/usr/bin/env python3
"""Report how much of the knowledge store is reusable and how comparable its
measurements are.

The report reads canonical objects, names and observations directly. Its
figures are bookkeeping about the published store, never proof, applicability or
profitability authority. A structural duplicate here means two entries share an
outline once value sorts are erased; it does not establish that either entry is
redundant, and an entry used by one program may still generalise.

    python3 tools/knowledge_health.py --root . -o build/knowledge-health
"""
import argparse
import hashlib
import json
import os
import re
import statistics
from collections import Counter, defaultdict
from pathlib import Path

SEMANTICS = 'ink-knowledge-health-v1'
CARRIER = re.compile(r'(?:[_/-](?:u8|u16|u32|u64|i8|i16|i32|i64|f32|f64|bool|word|int|nat))+$', re.I)
MULTI = object()


def read_objects(root):
    objects, sizes = {}, {}
    directory = root / 'store' / 'objects'
    for name in os.listdir(directory):
        if not name.endswith('.json'):
            continue
        raw = (directory / name).read_bytes()
        ident = name[:-5]
        objects[ident] = json.loads(raw)
        sizes[ident] = len(raw)
    return objects, sizes


def erase_sorts(value):
    """Outline of a term with value sorts and literal widths removed."""
    if isinstance(value, dict):
        return {k: ('*' if k == 'sort' else erase_sorts(v)) for k, v in value.items()}
    if isinstance(value, list):
        return [erase_sorts(v) for v in value]
    return value


def ownership(objects):
    """For each object, the single top-level entry that reaches it, or MULTI.

    Top-level entries are objects no other object depends on. Propagates over
    the dependency DAG from dependents to dependencies.
    """
    dependents = defaultdict(list)
    for ident, obj in objects.items():
        for dep in obj.get('dependencies', []):
            if dep in objects:
                dependents[dep].append(ident)
    owner = {}
    # Kahn order over the reversed graph: an object is ready once every
    # dependent has an owner.
    remaining = {ident: len(dependents[ident]) for ident in objects}
    ready = [ident for ident, count in remaining.items() if count == 0]
    for ident in ready:
        owner[ident] = ident
    order = list(ready)
    while order:
        ident = order.pop()
        for dep in objects[ident].get('dependencies', []):
            if dep not in objects:
                continue
            current = owner.get(dep)
            mine = owner[ident]
            owner[dep] = mine if current is None or current == mine else MULTI
            remaining[dep] -= 1
            if remaining[dep] == 0:
                order.append(dep)
    return owner, dependents


def term_size(term):
    node = term.get('node') if isinstance(term, dict) else None
    count = 1
    if isinstance(node, dict):
        if 'Op' in node:
            count += sum(term_size(a) for a in node['Op'][1])
        elif 'Lambda' in node:
            count += term_size(node['Lambda'])
        elif 'Cons' in node:
            count += sum(term_size(a) for a in node['Cons'])
    return count


def law_report(objects, names_by_id):
    rewrites = {i: o for i, o in objects.items() if o.get('kind') == 'rewrite'}
    general = {i for i, o in rewrites.items() if o.get('semantics') == 'ink-general-laws-v1'}
    instances = {i for i, o in rewrites.items() if i not in general and any(d in general for d in o.get('dependencies', []))}
    outlines = defaultdict(list)
    for ident, obj in rewrites.items():
        payload = obj.get('payload', {})
        outline = json.dumps(erase_sorts({k: payload.get(k) for k in ('from', 'to', 'conditions', 'params')}), sort_keys=True)
        outlines[hashlib.sha256(outline.encode()).hexdigest()].append(ident)
    groups = sorted(outlines.values(), key=len, reverse=True)
    stems = Counter()
    named = 0
    for ident in rewrites:
        for name in names_by_id.get(ident, []):
            named += 1
            stems[CARRIER.sub('', name)] += 1
            break
    sizes = sorted(term_size(o.get('payload', {}).get('from', {})) for i, o in rewrites.items() if i not in general)
    quantile = lambda q: sizes[int(q * (len(sizes) - 1))] if sizes else None
    conditions = Counter(len(o.get('payload', {}).get('conditions', [])) for o in rewrites.values())
    general_names = sorted({(names_by_id.get(i) or [i])[0].split('/')[0] for i in general})
    return dict(
        pattern_nodes=dict(median=quantile(.5), p75=quantile(.75), p90=quantile(.9), max=sizes[-1] if sizes else None,
                           over_10=sum(1 for v in sizes if v > 10), over_20=sum(1 for v in sizes if v > 20),
                           over_40=sum(1 for v in sizes if v > 40)),
        conditions_per_rewrite=dict(sorted(conditions.items())), general_law_families=general_names,
        rewrites=len(rewrites), general_laws=len(general), instances_of_general_laws=len(instances),
        concrete_laws_without_general_basis=len(rewrites) - len(general) - len(instances),
        sort_erased_outlines=len(outlines),
        rewrites_per_outline=round(len(rewrites) / max(1, len(outlines)), 3),
        largest_outline_groups=[dict(size=len(g), example=(names_by_id.get(g[0]) or [g[0]])[0]) for g in groups[:15]],
        named_rewrites=named, carrier_stripped_name_stems=len(stems),
        scope='Outlines erase value sorts only; equal outlines are candidates for one general law, not proven duplicates')


def observation_report(root):
    directory = root / 'store' / 'observations'
    cohorts = defaultdict(set)
    backend_variants = defaultdict(set)
    toolchains = set()
    null_peak = 0
    no_entries = 0
    samples = []
    entry_programs = defaultdict(set)
    total = 0
    if not directory.exists():
        return dict(observations=0)
    for name in os.listdir(directory):
        if not name.endswith('.json'):
            continue
        total += 1
        obs = json.loads((directory / name).read_bytes())
        target, workload = obs.get('target', {}), obs.get('workload', {})
        cohort = (obs.get('program'), json.dumps(target, sort_keys=True), json.dumps(workload, sort_keys=True))
        cohorts[cohort].add(obs.get('plan'))
        loose = (obs.get('program'), target.get('hardware'), target.get('driver'), json.dumps(workload, sort_keys=True))
        backend_variants[loose].add(target.get('backend'))
        toolchains.add(target.get('toolchain'))
        metrics = obs.get('metrics', {})
        if metrics.get('peak_bytes') is None:
            null_peak += 1
        values = metrics.get('complete_call_ns')
        samples.append(len(values) if isinstance(values, list) else 1)
        if not obs.get('entries'):
            no_entries += 1
        for entry in obs.get('entries', []):
            entry_programs[entry].add(obs.get('program'))
    comparable = sum(1 for plans in cohorts.values() if len(plans) > 1)
    split = sum(1 for backends in backend_variants.values() if len(backends) > 1)
    multi = sum(1 for programs in entry_programs.values() if len(programs) > 1)
    return dict(
        observations=total, cohorts=len(cohorts), cohorts_comparing_two_or_more_plans=comparable,
        single_plan_cohort_share=round(1 - comparable / max(1, len(cohorts)), 4),
        workload_groups_split_across_backend_labels=split, distinct_toolchains=len(toolchains),
        null_peak_bytes=null_peak, observations_without_entry_attribution=no_entries,
        median_samples_per_observation=statistics.median(samples) if samples else None,
        attributed_entries=len(entry_programs), entries_attributed_to_two_or_more_programs=multi,
        scope='Exact canonical target/workload matching, as Store.observations uses; a single-plan cohort cannot rank alternatives')


def report(root):
    objects, sizes = read_objects(root)
    names = json.loads((root / 'store' / 'names.json').read_text()) if (root / 'store' / 'names.json').exists() else {}
    names_by_id = defaultdict(list)
    for name, ident in names.items():
        if isinstance(ident, str):
            names_by_id[ident].append(name)
    kinds = Counter(); kind_bytes = Counter(); semantics = Counter()
    for ident, obj in objects.items():
        kinds[obj.get('kind')] += 1; kind_bytes[obj.get('kind')] += sizes[ident]
        semantics[obj.get('semantics')] += 1
    owner, dependents = ownership(objects)
    top = [i for i in objects if not dependents[i]]
    exclusive_bytes = Counter(); exclusive_count = Counter()
    for ident, root_id in owner.items():
        if root_id is MULTI or root_id == ident:
            continue
        exclusive_bytes[objects[root_id].get('kind')] += sizes[ident]
        exclusive_count[objects[root_id].get('kind')] += 1
    single_dependent = Counter(obj.get('kind') for i, obj in objects.items() if len(dependents[i]) == 1)
    no_dependent = Counter(obj.get('kind') for i, obj in objects.items() if not dependents[i])
    edges = sum(len(o.get('dependencies', [])) for o in objects.values())
    total_bytes = sum(sizes.values())
    snapshots = len(list((root / 'store' / 'snapshots').glob('*.json'))) if (root / 'store' / 'snapshots').exists() else 0
    return dict(
        schema=1, semantics=SEMANTICS,
        scope='Bookkeeping over published bytes; no proof, applicability or profitability authority',
        objects=dict(count=len(objects), bytes=total_bytes, by_kind={k: dict(count=kinds[k], bytes=kind_bytes[k]) for k in sorted(kinds, key=str)},
                     by_semantics=dict(semantics.most_common()), snapshots=snapshots),
        dependencies=dict(edges=edges, top_level_entries=len(top),
                          without_dependents_by_kind=dict(no_dependent), single_dependent_by_kind=dict(single_dependent),
                          exclusively_owned_by_root_kind={k: dict(objects=exclusive_count[k], bytes=exclusive_bytes[k],
                                                                  share_of_store=round(exclusive_bytes[k] / max(1, total_bytes), 4))
                                                          for k in sorted(exclusive_bytes, key=str)},
                          shared_objects=sum(1 for v in owner.values() if v is MULTI)),
        laws=law_report(objects, names_by_id),
        measurements=observation_report(root))


def markdown(value):
    o, d, l, m = value['objects'], value['dependencies'], value['laws'], value['measurements']
    lines = ['# Knowledge health', '',
             f"{o['count']:,} objects, {o['bytes'] / 1e6:.1f} MB, {o['snapshots']} snapshots; {d['edges']:,} dependency edges.", '',
             '| Kind | Objects | MB | Without dependents | One dependent |', '|---|---:|---:|---:|---:|']
    for kind, row in o['by_kind'].items():
        lines.append(f"| {kind} | {row['count']:,} | {row['bytes'] / 1e6:.1f} | {d['without_dependents_by_kind'].get(kind, 0):,} | {d['single_dependent_by_kind'].get(kind, 0):,} |")
    lines += ['', '## Bytes reachable from only one top-level entry', '', '| Owning entry kind | Objects | MB | Share of store |', '|---|---:|---:|---:|']
    for kind, row in d['exclusively_owned_by_root_kind'].items():
        lines.append(f"| {kind} | {row['objects']:,} | {row['bytes'] / 1e6:.1f} | {row['share_of_store']:.0%} |")
    lines += ['', '## Laws', '',
              f"- {l['rewrites']:,} rewrites: {l['general_laws']} general laws, {l['instances_of_general_laws']} instances of them, "
              f"{l['concrete_laws_without_general_basis']:,} concrete laws with no general basis.",
              f"- {l['sort_erased_outlines']:,} distinct outlines once value sorts are erased ({l['rewrites_per_outline']} rewrites per outline).",
              f"- {l['named_rewrites']:,} named rewrites reduce to {l['carrier_stripped_name_stems']:,} name stems without carrier suffixes.",
              f"- General-law families: {', '.join(l['general_law_families']) or 'none'}.",
              f"- Left-hand patterns: median {l['pattern_nodes']['median']} nodes, 90th percentile {l['pattern_nodes']['p90']}, "
              f"maximum {l['pattern_nodes']['max']}; {l['pattern_nodes']['over_20']:,} exceed 20 nodes.",
              f"- Conditions per rewrite: " + ', '.join(f"{k}: {v:,}" for k, v in l['conditions_per_rewrite'].items()) + '.', '',
              '| Largest same-outline groups | Rewrites |', '|---|---:|']
    for row in l['largest_outline_groups'][:10]:
        lines.append(f"| `{row['example']}` | {row['size']} |")
    lines += ['', '## Measurements', '',
              f"- {m.get('observations', 0):,} observations in {m.get('cohorts', 0):,} exact (program, target, workload) cohorts; "
              f"{m.get('cohorts_comparing_two_or_more_plans', 0):,} compare two or more plans ({1 - m.get('single_plan_cohort_share', 1):.1%}).",
              f"- {m.get('workload_groups_split_across_backend_labels', 0):,} workload groups appear under more than one backend label, which exact matching cannot compare.",
              f"- {m.get('distinct_toolchains', 0)} distinct toolchain strings; {m.get('null_peak_bytes', 0):,} observations without peak bytes; "
              f"{m.get('observations_without_entry_attribution', 0):,} without entry attribution.",
              f"- {m.get('attributed_entries', 0)} attributed entries, {m.get('entries_attributed_to_two_or_more_programs', 0)} of them across two or more programs.", '',
              value['scope'] + '.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('-o', '--output', type=Path, required=True)
    args = parser.parse_args()
    value = report(args.root.resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'health.json').write_text(json.dumps(value, indent=2) + '\n')
    (args.output / 'health.md').write_text(markdown(value))
    print(json.dumps(dict(objects=value['objects']['count'], rewrites=value['laws']['rewrites'],
                          outlines=value['laws']['sort_erased_outlines'],
                          single_plan_cohort_share=value['measurements'].get('single_plan_cohort_share'))))


if __name__ == '__main__':
    main()
