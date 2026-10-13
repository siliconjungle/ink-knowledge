"""Author ordinary bidirectional proofs for compiler-exported sum codecs.

No JSON shape, constructor spelling, profile or theorem hash grants authority.
These proofs preserve arbitrary opaque leaf values, including recursive carriers.
"""
import argparse
import json
import subprocess
import tempfile
from pathlib import Path
from ink_knowledge import Store, identity
from ink_knowledge.store import entry
from producers.physical_capabilities import base, invoke, write
from producers.workspace import compiler_path

MATH = 'first-order-inductive-equality-v1'
def var(name): return {'Var': name}
def call(name, value): return {'Call': {'function': name, 'arguments': [value]}}
def construct(name, index, value):
    return {'Construct': {'datatype': name, 'constructor': index, 'arguments': [value]}}
def convert(left, right): return {'Convert': {'from': left, 'to': right}}

def codec_objects(schema):
    chain = schema['source_chain']
    flat = schema['flat']
    enc = lambda x: call(schema['encode'], x)
    dec = lambda x: call(schema['decode'], x)
    roundtrip = lambda x: dec(enc(x))
    def embed(at, value):
        for index in reversed(range(at)):
            value = construct(chain[index], 1, value)
        return value
    def source_cases(at, name):
        value = embed(at, var(name))
        left_name, right_name = f'leaf{at}', f'tail{at}'
        left = embed(at, construct(chain[at], 0, var(left_name)))
        right = embed(at, construct(chain[at], 1, var(right_name)))
        last = at + 1 == len(chain)
        return {'Cases': {'variable': name, 'from': roundtrip(value), 'to': value,
            'cases': [
                {'bindings': [left_name], 'proof': convert(roundtrip(left), left)},
                {'bindings': [right_name], 'proof': convert(roundtrip(right), right) if last else source_cases(at + 1, right_name)},
            ]}}
    source = var('source')
    compact = var('flat')
    inverse = lambda x: enc(dec(x))
    cases = []
    for index in range(len(schema['alternatives'])):
        name = f'leaf{index}'
        node = construct(flat, index, var(name))
        cases.append({'bindings': [name], 'proof': convert(inverse(node), node)})
    proofs = [
        ([['source', schema['source']]], roundtrip(source), source, source_cases(0, 'source')),
        ([['flat', {'Data': flat}]], inverse(compact), compact,
         {'Cases': {'variable': 'flat', 'from': inverse(compact), 'to': compact, 'cases': cases}}),
    ]
    objects = list(schema['entries'].values())
    roots = []
    for params, left, right, proof in proofs:
        theorem = entry('theorem', MATH, {'declaration': {'Theorem': {
            'params': params, 'conditions': [], 'from': left, 'to': right, 'proof': proof,
        }}}, list(schema['entries']), parameters=dict(params))
        objects.append(theorem)
        roots.append(identity(theorem))
    return objects, roots

def produce(source, compiler, directory, source_core=False, publish=None):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    flags = ['--core'] if source_core else []
    with tempfile.TemporaryDirectory(prefix='ink-sum-codecs-') as scratch:
        output = Path(scratch) / 'schemas.json'
        invoke(compiler, 'emit-sum-codecs', source, *flags, '-o', output)
        schemas = json.loads(output.read_bytes())
    objects, layouts = [], []
    for schema in schemas:
        authored, roots = codec_objects(schema)
        objects.extend(authored)
        layouts.append({'sum_type': schema['sum_type'], 'roundtrip': roots[0], 'inverse': roots[1]})
    if not layouts:
        return []
    store = Store.publish(directory, list({identity(o): o for o in objects}.values()))
    for index, layout in enumerate(layouts):
        layout['knowledge'] = store.bundle([layout['roundtrip'], layout['inverse']])
        path = write(directory / f'layout-{index}.json', layout)
        invoke(compiler, 'check-sum-codec', source, path, *flags)
    write(directory / 'layouts.json', layouts)
    if publish is not None:
        publication = Store(publish)
        names_path = publication.data / 'names.json'
        names = json.loads(names_path.read_bytes()) if names_path.exists() else {}
        for layout in layouts:
            key = identity(layout['sum_type'])
            names['sum-codec/' + key + '/roundtrip'] = layout['roundtrip']
            names['sum-codec/' + key + '/inverse'] = layout['inverse']
        publication.extend(list({identity(o): o for o in objects}.values()), names).ensure_index()
    return layouts

def candidates(context, groupings=('all', 'individual')):
    if context.get('representation') or context.get('emit_target') != 'javascript':
        yield dict(status='declined', label='sum-spine', reason='requires source JavaScript carrier')
        return
    with tempfile.TemporaryDirectory(prefix='ink-sum-recipe-') as scratch:
        directory = Path(scratch)
        source = write(directory / 'source.json', context['core'])
        layouts = produce(source, context['compiler'], directory / 'proofs', True)
        if not layouts:
            return
        current = context.get('physical')
        if current is None:
            subjects = directory / 'subjects.json'
            invoke(context['compiler'], 'emit-bounds-obligations', source, '--core', '-o', subjects)
            current = base(json.loads(subjects.read_bytes())['source'])
        existing = {json.dumps(v['sum_type'], sort_keys=True): v for v in current.get('sum_spines', [])}
        choices = []
        if 'individual' in groupings:
            choices.extend((str(index), [layout]) for index, layout in enumerate(layouts))
        if 'all' in groupings:
            choices.append(('all', layouts))
        for label, additions in choices:
            merged = dict(existing)
            merged.update((json.dumps(v['sum_type'], sort_keys=True), v) for v in additions)
            if merged == existing:
                continue
            plan = json.loads(json.dumps(current))
            # Core orders by its serialized source Type, not descriptor keys.
            plan['sum_spines'] = sorted(merged.values(), key=lambda v: json.dumps(v['sum_type'], separators=(',', ':')))
            invoke(context['compiler'], 'check-physical-plan', source, write(directory / 'physical.json', plan), '--core')
            yield dict(status='proposal', label='sum-spine/' + label, step=dict(kind='physical', package=plan))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--compiler', type=Path, default=compiler_path())
    parser.add_argument('-o', type=Path, required=True)
    parser.add_argument('--core', action='store_true')
    parser.add_argument('--publish', type=Path, help='Extend an existing canonical publication after all codec proofs replay')
    args = parser.parse_args()
    layouts = produce(args.source, args.compiler, args.o, args.core, args.publish)
    print(json.dumps({'status': 'checked', 'sums': len(layouts)}))

if __name__ == '__main__':
    main()
