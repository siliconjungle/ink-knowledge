#!/usr/bin/env python3
"""Publish exact transport-boundary timings for the existing lifecycle planner.

These are operational codec alternatives, not source rewrite certificates. Every
adapter still validates the complete schema. Evidence ranks only the measured
fixture, workload shape, phase, target, and exact ABI/source fingerprint.
"""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from ink_knowledge import Store,canonical,identity

LABELS={'carrier-json-to-wire','stream-json-to-wire','materialize-wire','borrow-wire','index-wire','pack-wire','materialized','borrowed','indexed','packed'}

def publish(root,report,target,abi_fingerprint,fixture_fingerprint):
    if report.get('schema')!=1 or report.get('instrumented')is not False or report.get('fixture')!='List<u32>':
        raise ValueError('requires ordinary schema-bound benchmark report')
    for fingerprint in (abi_fingerprint,fixture_fingerprint):
        if len(fingerprint)!=64 or any(c not in '0123456789abcdef'for c in fingerprint):raise ValueError('exact code fingerprint required')
    store=Store(root)if Store.is_published(Path(root))else Store.publish(root,[])
    source=identity(dict(fixture=report['fixture'],code=fixture_fingerprint))
    plans={label:identity(dict(schema=1,semantics='ink-value-boundary-measurement-v1',candidate=label,abi=abi_fingerprint,fixture=fixture_fingerprint))for label in sorted(LABELS)}
    observations=[];groups={}
    for row in report['measurements']:
        label=row['candidate'];phase=row['phase'];reads=row.get('reads',0)
        if label not in plans or phase not in {'construct','read','lifecycle'} or type(row['rows'])is not int or not 0<row['rows']<=1000000 or type(reads)is not int or not 0<=reads<=1000000:raise ValueError('bounded measured shape required')
        operation='json-to-wire'if label.endswith('json-to-wire')else 'typed-wire-access'
        workload=dict(shape=dict(rows=row['rows'],reads=reads,input_bytes=row['input_bytes']),distribution=dict(operation=operation,fixture=fixture_fingerprint),concurrency=1,residency='validated immutable wire; setup included'if phase!='read'else'validated immutable wire; preconstructed representation')
        samples=row['samples_ns']
        if len(samples)<9 or any(int(n)<=0 for n in samples):raise ValueError('positive repeated boundary timings required')
        observation=dict(schema=1,program=source,entries=[],plan=plans[label],target=target,workload={**workload,'distribution':dict(workload=workload['distribution'],phase=phase)},metrics=dict(complete_call_ns=samples,peak_bytes=None))
        ident=store.observe(observation);observations.append(ident)
        key=identity([workload,phase]);group=groups.setdefault(key,dict(workload=workload,phase=phase,candidates={}))
        group['candidates'][label]=plans[label]
    return dict(schema=1,snapshot=store.snapshot_id,program=source,target=target,abi_fingerprint=abi_fingerprint,fixture_fingerprint=fixture_fingerprint,observations=observations,groups=list(groups.values()),scope='Exact measured boundaries only. Source equality, backend correctness, shape applicability and profitability remain separate. Peak memory is unmeasured.')

def select(store,manifest):
    """Use existing generic lifecycle ranking, with no codec dispatch in planner."""
    from ink_planner.representation_selection import rank
    decisions=[]
    for group in manifest['groups']:
        candidates=group['candidates'];phase=group['phase']
        baseline='carrier-json-to-wire'if'carrier-json-to-wire'in candidates else 'materialized'if'materialized'in candidates else 'materialize-wire'
        if baseline not in candidates:continue
        ids=list(candidates.values());chosen,receipt=rank(store,manifest['program'],ids,manifest['target'],group['workload'],{phase:1},candidates[baseline])
        decisions.append(dict(phase=phase,workload=group['workload'],selected=next(label for label,ident in candidates.items()if ident==chosen),baseline=baseline,receipt=receipt))
    return decisions

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True);p.add_argument('--report',type=Path,required=True);p.add_argument('--target',type=Path,required=True);p.add_argument('--abi-root',type=Path,required=True);p.add_argument('--fixture',type=Path,required=True);p.add_argument('--planner-root',type=Path,required=True);p.add_argument('-o',type=Path,required=True);a=p.parse_args()
    digest=hashlib.sha256()
    for path in sorted((a.abi_root/'src').glob('*')):
        if path.is_file():digest.update(path.name.encode());digest.update(path.read_bytes())
    for name in ('Cargo.toml','Cargo.lock'):digest.update((a.abi_root/name).read_bytes())
    manifest=publish(a.root,json.loads(a.report.read_bytes()),json.loads(a.target.read_bytes()),digest.hexdigest(),hashlib.sha256(a.fixture.read_bytes()).hexdigest())
    sys.path.insert(0,str(a.planner_root));manifest['selection']=select(Store(a.root),manifest)
    a.o.parent.mkdir(parents=True,exist_ok=True);a.o.write_bytes(canonical(manifest)+b'\n');print(json.dumps(dict(observations=len(manifest['observations']),selection=len(manifest['selection']),snapshot=manifest['snapshot'])))
if __name__=='__main__':main()
