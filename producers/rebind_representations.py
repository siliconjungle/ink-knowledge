#!/usr/bin/env python3
"""Replay existing representation proofs against an identical action projection.

Projection equality is an authoring eligibility restriction. Every proposed new
source binding must still pass ordinary universal representation admission.
"""
import argparse, hashlib, json, subprocess, sys, tempfile
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import canonical
from ink_knowledge.store import read

def replay(compiler, source, paths):
    compiler, source = Path(compiler).resolve(), Path(source).resolve()
    def run(*args):
        return json.loads(subprocess.run([str(compiler), *map(str, args)],
            capture_output=True, text=True, check=True, timeout=60).stdout)
    with tempfile.TemporaryDirectory(prefix='ink-representation-rebind-') as tmp:
        tmp = Path(tmp)
        run('emit-action-model', source, '-o', tmp / 'model.json')
        model = read(tmp / 'model.json')
        proposals, receipts = [], []
        for at, path in enumerate(paths):
            path = Path(path); request = read(path)
            plan = request['knowledge']['objects'][request['representation']]['payload']
            if set(plan['source_objects']) != set(model['objects']) or any(
                    request['knowledge']['objects'].get(i) != obj for i, obj in model['objects'].items()):
                raise ValueError('action projection differs; re-author rather than rebind: ' + str(path))
            proposal = {**request, 'input_core_sha256': model['source']}
            raw = canonical(proposal) + b'\n'; staged = tmp / (str(at) + '.json'); staged.write_bytes(raw)
            checked = run('check-representation', source, staged)
            if (checked.get('status'), checked.get('source'), checked.get('representation')) != (
                    'checked', model['source'], request['representation']):
                raise ValueError('rebind admission receipt mismatch')
            proposals.append((path, raw))
            receipts.append(dict(path=str(path), representation=request['representation'],
                previous_source=request['input_core_sha256'], source=model['source'],
                request_sha256=hashlib.sha256(raw).hexdigest(), obligations=len(checked['obligations'])))
        for path, raw in proposals:
            path.write_bytes(raw)
        return dict(schema=1, status='checked', compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                    source_path=str(source), requests=receipts,
                    scope='Identical complete action projection; ordinary universal checking replayed for every proposed source binding')

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiler', type=Path, required=True)
    p.add_argument('--source', type=Path, required=True)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('requests', nargs='+', type=Path)
    a = p.parse_args(); result = replay(a.compiler, a.source, a.requests)
    a.report.write_bytes(canonical(result) + b'\n')
    print(json.dumps(dict(status='checked', requests=len(result['requests']))))
