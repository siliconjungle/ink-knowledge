#!/usr/bin/env python3
"""Publish separately authored Ink laws through ordinary checked canonical entries."""
import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, canonical


def publish(compiler, source, output, proofs=None, dependencies=None):
    output = Path(output)
    with tempfile.TemporaryDirectory(prefix='ink-source-laws-') as directory:
        bundle_path = Path(directory) / 'bundle.json'
        command = [str(compiler), 'emit-laws', str(source), '-o', str(bundle_path)]
        if proofs:
            command += ['--proofs', str(proofs)]
        if dependencies:
            command += ['--view', str(dependencies)]
        completed = subprocess.run(command, capture_output=True, text=True, timeout=60)
        if completed.returncode:
            raise ValueError("law authoring rejected: " + completed.stderr.strip())
        receipt = json.loads(completed.stdout)
        bundle = json.loads(bundle_path.read_text())
    objects, names, roots = [], {}, []
    if Store.is_published(output):
        previous = Store(output)
        objects = [previous.object(key) for key in previous.members()]
        names = previous.names
        roots = json.loads((output / 'store/rewrite-view.json').read_text())['roots']
    objects += list(bundle['objects'].values())
    names.update({'rewrite/source/' + name: key for name, key in receipt['names'].items()})
    roots += bundle['roots']
    store = Store.publish(output, objects, names)
    store.rebuild()
    (output / 'store/rewrite-view.json').write_bytes(canonical(store.bundle(sorted(set(roots)))) + b'\n')
    (output / 'store/source-law-view.json').write_bytes(canonical(store.bundle(bundle['roots'])) + b'\n')
    return {'laws': len(bundle['roots']), 'snapshot': store.snapshot_id, 'names': receipt['names']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--proofs', type=Path)
    parser.add_argument('--dependencies', type=Path)
    parser.add_argument('--output-store', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(publish(args.compiler, args.source, args.output_store, args.proofs, args.dependencies)))
