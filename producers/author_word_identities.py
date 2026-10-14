"""Offline certificate authoring and checked publication for word templates."""
import argparse
import gzip
import hashlib
import json
import os
import subprocess
import tempfile
import time
from pathlib import Path
from ink_knowledge import Store, canonical, identity, semantic_entry
from .bitvector_proofs import certificate
from .semantic_laws import law
from .word_identities import templates


def update_frozen_data(path, rows):
    """Checked additions must not erase laws from an earlier authoring run."""
    path = Path(path)
    existing = json.loads(gzip.decompress(path.read_bytes())) if path.exists() else []
    merged = {row['name']: row for row in existing}
    if len(merged) != len(existing):
        raise ValueError('Duplicate names in frozen word laws')
    for row in rows:
        merged[row['name']] = dict(name=row['name'], law=row['law'])
    data = [merged[name] for name in sorted(merged)]
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.word-laws-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(gzip.compress(canonical(data), mtime=0))
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary): os.unlink(temporary)
    return len(data)


def checked_law(compiler, core, goal, directory, seconds=10):
    request, cnf = directory / 'goal.json', directory / 'cnf.json'
    request.write_bytes(canonical(goal))
    result = subprocess.run([str(compiler), 'semantic-bitvector-obligation', str(core),
                             str(request), '--core', '-o', str(cnf)],
                            capture_output=True, text=True, timeout=60)
    if result.returncode:
        raise ValueError(result.stderr[-4000:])
    problem = json.loads(cnf.read_bytes())
    proof = certificate(problem, seconds=seconds, conflicts=100000, total_seconds=seconds)
    candidate = law(goal['params'], goal['from'], goal['to'],
                    {'BitVector': {'hypotheses': list(range(len(goal['conditions']))),
                                   'certificate': proof}}, conditions=goal['conditions'])
    obj = semantic_entry(candidate)
    st = Store.publish(directory / 'candidate', [obj])
    view = directory / 'view.json'
    view.write_bytes(canonical(st.bundle([identity(obj)])))
    result = subprocess.run([str(compiler), 'knowledge-check', str(core), str(view)],
                            capture_output=True, text=True, timeout=60)
    if result.returncode:
        raise ValueError(result.stderr[-4000:])
    return candidate, dict(variables=problem['variables'], clauses=len(problem['clauses']),
                           proof_steps=len(proof['steps']), admission=json.loads(result.stdout))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiler', type=Path, required=True)
    p.add_argument('--output-store', type=Path, required=True)
    p.add_argument('--data', type=Path, required=True)
    p.add_argument('--seconds', type=int, default=10)
    p.add_argument('--case', action='append')
    a = p.parse_args()
    if not 1 <= a.seconds <= 120:
        p.error('seconds must be in 1..120')
    compiler = a.compiler.resolve()
    compiler_hash = hashlib.sha256(compiler.read_bytes()).hexdigest()
    rows, failures = [], []
    requested = templates()
    if a.case:
        unknown = set(a.case) - {row['name'] for row in requested}
        if unknown:
            p.error('unknown cases: ' + ', '.join(sorted(unknown)))
        requested = [row for row in requested if row['name'] in a.case]
    with tempfile.TemporaryDirectory(prefix='ink-word-identities-') as tmp:
        d = Path(tmp)
        source, core = d / 'source.ink', d / 'core.json'
        source.write_text('module word_identity_authoring; fn identity(x:u32)->u32{return x;}\n')
        subprocess.run([str(compiler), 'emit-core', str(source), '-o', str(core)],
                       check=True, capture_output=True, timeout=60)
        for i, row in enumerate(requested):
            case = d / str(i); case.mkdir()
            start = time.monotonic()
            try:
                candidate, receipt = checked_law(compiler, core, row['goal'], case, a.seconds)
                rows.append(dict(name=row['name'], law=candidate, evidence=receipt))
                print(json.dumps(dict(name=row['name'], status='checked',
                                      seconds=time.monotonic()-start)), flush=True)
            except (ValueError, subprocess.TimeoutExpired) as error:
                failures.append(dict(name=row['name'], reason=str(error)))
                print(json.dumps(dict(name=row['name'], status='unadmitted', reason=str(error))), flush=True)
        if hashlib.sha256(compiler.read_bytes()).hexdigest() != compiler_hash:
            raise ValueError('Compiler changed during certificate authoring')
        # Receipts contain timings/diagnostics; immutable runtime data contains
        # only reusable laws and names, without source-specific authoring state.
        frozen_count = update_frozen_data(a.data, rows)
        objects = [semantic_entry(r['law']) for r in rows]
        names = {'word-identities/'+r['name']: identity(semantic_entry(r['law'])) for r in rows}
        store = (Store(a.output_store).extend(objects, names) if (a.output_store/'store/snapshot.json').exists()
                 else Store.publish(a.output_store, objects, names))
        receipt = dict(compiler_sha256=compiler_hash, requested=len(requested), checked=len(rows),
                       frozen_laws=frozen_count, failures=failures, snapshot=store.snapshot_id, rows=rows)
        (a.output_store / 'authoring.json').write_bytes(canonical(receipt))
        print(json.dumps({k: v for k, v in receipt.items() if k != 'rows'}))


if __name__ == '__main__':
    main()
