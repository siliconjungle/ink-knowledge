"""Bind untimed target-work trace rows to exact semantic/target provenance.
No counts are inferred from list lengths or from source operation names.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path

ACQUISITION_BINDINGS = ('instrumenter', 'runner', 'parser', 'boundary_runner', 'boundary_extractor', 'boundary_adapter')

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''): digest.update(block)
    return digest.hexdigest()


def produce(output, paths, cohort):
    with Path(paths['trace']).open('rb') as stream: raw = stream.read(64_000_001)
    if len(raw) > 64_000_000: raise ValueError('physical trace byte budget')
    trace = json.loads(raw)
    if not isinstance(trace, dict): raise ValueError('physical trace object required')
    if trace.get('status') != 'untimed-complete-output-replayed': raise ValueError('untimed oracle replay required')
    if not isinstance(trace.get('rows'), list) or len(trace['rows']) > 4096 or any(not isinstance(row, dict) for row in trace['rows']): raise ValueError('physical trace row budget')
    output = Path(output); output.mkdir(parents=True, exist_ok=True)
    bindings = {name: dict(path=os.path.relpath(Path(path).resolve(), output.resolve()), sha256=hashlib.sha256(raw).hexdigest() if name == 'trace' else sha(path)) for name, path in paths.items()}
    # Prices fitted to a different collector cannot interpret this vector. Keep
    # acquisition definitions separate from artifact/fixture-specific identities.
    cohort = copy.deepcopy(cohort)
    cohort['acquisition'] = {name: bindings[name]['sha256'] for name in ACQUISITION_BINDINGS if name in bindings}
    if not {'instrumenter', 'runner'} <= set(cohort['acquisition']): raise ValueError('physical acquisition bindings required')
    rows = []
    for i, row in enumerate(trace['rows']):
        if row['boundary'] != cohort['boundary']: continue
        data = dict(schema=1, kind='ink-target-work-v1', cohort=cohort, bindings=bindings,
                    entry=row['entry'], fixture_id=row['id'], components=row['components'],
                    known=row['known'], unknown=row['unknown'], scope=trace['scope'])
        path=output/f'{i:04}.json'; path.write_text(json.dumps(data,indent=2)+'\n')
        rows.append(dict(path=str(path),entry=row['entry'],fixture_id=row['id']))
    return rows


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('original-core','selected-core','selection','artifact','fixture','instrumenter','instrumented','instrumentation','runner','trace','cohort','output'):
        p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args()
    fields=('original_core','selected_core','selection','artifact','fixture','instrumenter','instrumented','instrumentation','runner','trace')
    rows=produce(a.output,{k:getattr(a,k)for k in fields},json.loads(a.cohort.read_text()))
    print(json.dumps(dict(sidecars=len(rows),scope='Untimed offline source-bound diagnostic observations, not proof authority')))
if __name__=='__main__':main()
