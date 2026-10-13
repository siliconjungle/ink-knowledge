#!/usr/bin/env python3
"""Re-certify `key_equal_reflexive` after a checker normalisation change.

The checker normalises a bit-vector goal before building its CNF. It now folds
`x == x` to `true`, so the 128-bit circuit these packages certified is no
longer the problem the checker builds, and `verify-library` rejects the stored
certificate. The theorem statement is unchanged: this script asks the compiler
for the current obligation (`key_reflexive.goal.json`), proves it with the
ordinary producer, rewrites the one object, and renames its identity wherever
the package records it. No other object depends on it.

The compiler decides validity: every rewritten package is re-verified with
`verify-library`, and the discovery catalogue is rebuilt from the new locks.
"""
import argparse, hashlib, json, re, subprocess, sys, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from producers.bitvector_proofs import certificate  # noqa: E402

HEX = re.compile(r'^[0-9a-f]{64}$')
STYLES = [dict(indent=2), dict(), dict(separators=(',', ':')), dict(indent=2, sort_keys=True),
          dict(sort_keys=True), dict(separators=(',', ':'), sort_keys=True)]


def style_of(raw):
    value = json.loads(raw)
    for style in STYLES:
        for newline in ('\n', ''):
            if json.dumps(value, **style) + newline == raw:
                return value, style, newline
    raise ValueError('unrecognised JSON formatting')


def rename(value, old, new, old_raw, new_raw):
    if isinstance(value, dict):
        out = {}
        for k, v in value.items():
            key = new if k == old else k
            out[key] = new_raw if (k == old and v == old_raw) else rename(v, old, new, old_raw, new_raw)
        return out
    if isinstance(value, list):
        items = [rename(v, old, new, old_raw, new_raw) for v in value]
        was_sorted = all(isinstance(v, str) and HEX.match(v) for v in value) and value == sorted(value)
        return sorted(items) if was_sorted else items
    return new if value == old else value


def certify(cert):
    if isinstance(cert, dict):
        if 'BitVector' in cert and cert['BitVector']['from'] is not None:
            yield cert['BitVector']
        for v in cert.values():
            yield from certify(v)
    elif isinstance(cert, list):
        for v in cert:
            yield from certify(v)


def repair(package, compiler):
    names = json.loads((package/'names.json').read_text())
    old = names['key_equal_reflexive']
    path = package/'objects'/f'{old}.json'
    old_raw = path.read_text()
    obj = json.loads(old_raw)
    with tempfile.TemporaryDirectory() as scratch:
        cnf = Path(scratch)/'cnf.json'
        subprocess.run([str(compiler), 'bitvector-obligation', str(package/'key_reflexive.goal.json'), '-o', str(cnf)],
                       check=True, capture_output=True)
        problem = json.loads(cnf.read_text())
    proofs = list(certify(obj['declaration']))
    if len(proofs) != 1:
        raise ValueError(f'{package}: expected one bit-vector proof, found {len(proofs)}')
    if proofs[0]['certificate']['problem_sha256'] == problem['sha256']:
        return None
    proofs[0]['certificate'] = certificate(problem)
    new_raw = json.dumps(obj, separators=(',', ':'), ensure_ascii=False) + '\n'
    new = hashlib.sha256(new_raw.encode()).hexdigest()
    (package/'objects'/f'{new}.json').write_text(new_raw)
    path.unlink()
    (package/'key_reflexive.cnf.json').write_text(json.dumps(problem) + '\n')
    for meta in sorted(package.glob('*.json')):
        raw = meta.read_text()
        if old not in raw:
            continue
        value, style, newline = style_of(raw)
        meta.write_text(json.dumps(rename(value, old, new, old_raw, new_raw), **style) + newline)
    if old in ''.join(p.read_text() for p in package.rglob('*.json')):
        raise ValueError(f'{package}: stale identity remains')
    subprocess.run([str(compiler), 'verify-library', str(package/'lock.json')], check=True, capture_output=True)
    return old, new


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    for goal in sorted(ROOT.rglob('key_reflexive.goal.json')):
        result = repair(goal.parent, compiler)
        print(goal.parent.relative_to(ROOT), 'unchanged' if result is None else f'{result[0][:12]} -> {result[1][:12]}')
    subprocess.run([sys.executable, str(ROOT/'catalogue.py'), 'rebuild'], check=True)


if __name__ == '__main__':
    main()
