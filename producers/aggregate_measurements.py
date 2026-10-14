#!/usr/bin/env python3
"""Store whole-batch timings as immutable, workload-specific selection evidence.

A batch phase describes the exact measured read/write mix and call count. It is
not an estimate of individual actions. Checking/compilation/initialisation remain
separate lifecycle phases. Evidence never grants representation admission.
"""
import argparse,hashlib,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, identity

def publish(reports,requests,target,directory,compilation=None,candidate_ids=None,compiler_sha256=None):
    store=Store(directory) if Store.is_published(directory) else Store.publish(directory,[])
    candidates={}
    packages={candidate:store.object(candidate)['payload']['package'] for candidate in (candidate_ids or {}).values()}
    for report in reports:
        data=json.loads(Path(report).read_text())
        if data.get('schema')not in (2,4) or data.get('instrumented',False):
            raise ValueError('selection requires ordinary uninstrumented whole-call timings')
        for row in data['measurements']:
            label=row['candidate']
            if candidate_ids and label not in candidate_ids:continue
            raw=(requests/(label+'.json')).read_bytes();request=json.loads(raw)
            request_hash=hashlib.sha256(raw).hexdigest();source=request['input_core_sha256']
            if candidate_ids:
                package=packages[candidate_ids[label]]
                if package.get('input_core_sha256')!=source or package.get('representation')!=request['representation']:raise ValueError('measurement candidate/source binding mismatch')
                if 'ordinary-source' in candidate_ids and packages[candidate_ids['ordinary-source']].get('input_core_sha256')!=source:raise ValueError('measurement baseline/source binding mismatch')
            plan=identity(dict(schema=1,semantics='ink-implementation-measurement-v1',candidate=candidate_ids[label],compiler_sha256=compiler_sha256,emission_target=target['backend'])) if candidate_ids else request_hash
            candidates[label]=dict(request_sha256=request_hash,measurement=plan,representation=request['representation'],source=source)
            workload=dict(shape=dict(rows=row['rows'],calls=row['calls_per_sample']),
                distribution=dict(query=row['query'],read_percent=row['read_percent'],script='bench/point-delta/standalone-aggregate.rs.txt'),
                concurrency=1,residency='restored; acknowledgement after every call')
            def observe(phase,samples):
                entries=[candidate_ids['ordinary-source'] if plan!=original_plan else candidate_ids[label]] if candidate_ids else []
                return store.observe(dict(schema=1,program=source,entries=entries,plan=plan,target=target,
                    workload={**workload,'distribution':dict(workload=workload['distribution'],phase=phase)},
                    metrics=dict(complete_call_ns=[str(n)for n in samples],peak_bytes=None)))
            original_plan=plan
            observe('action:batch_calls',[sample['native_ns']for sample in row['samples']])
            if candidate_ids and 'ordinary-source' in candidate_ids:
                original_plan=plan
                plan=identity(dict(schema=1,semantics='ink-implementation-measurement-v1',candidate=candidate_ids['ordinary-source'],compiler_sha256=compiler_sha256,emission_target=target['backend']))
                observe('action:batch_calls',[sample['ordinary_compiled_ink_ns']for sample in row['samples']])
                plan=original_plan
            initial=[p['initialise_ns']for p in data['phases']if p['rows']==row['rows']and p['candidate']==label]
            if initial:observe('initialise',initial)
            if compilation:
                checks=[p['check_ns']for p in compilation if p.get('candidate')==label]
                if checks:observe('check',checks)
    store.refresh_index()
    manifest=dict(schema=1,snapshot=store.snapshot_id,target=target,candidates=candidates,
        compiler_sha256=compiler_sha256,candidate_ids=candidate_ids,scope='measured whole batches; exact query/read mix and row/call counts only; portable migration and unmeasured memory require independent evidence')
    (directory/'aggregate-measurements.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('reports',type=Path,nargs='+');p.add_argument('--requests',type=Path,required=True);p.add_argument('--target',type=Path,required=True);p.add_argument('--compilation',type=Path);p.add_argument('--candidate-publication',type=Path);p.add_argument('--compiler',type=Path);p.add_argument('-o','--output',type=Path,required=True);a=p.parse_args()
    if bool(a.candidate_publication)!=bool(a.compiler):p.error('candidate publication and exact compiler are required together')
    publication=json.loads(a.candidate_publication.read_text())if a.candidate_publication else None
    print(json.dumps(publish(a.reports,a.requests,json.loads(a.target.read_text()),a.output,json.loads(a.compilation.read_text())if a.compilation else None,publication['candidates']if publication else None,hashlib.sha256(a.compiler.read_bytes()).hexdigest()if a.compiler else None)))
