#!/usr/bin/env python3
"""Store whole-batch timings as immutable, workload-specific selection evidence.

A batch phase describes the exact measured read/write mix and call count. It is
not an estimate of individual actions. Checking/compilation/initialisation remain
separate lifecycle phases. Evidence never grants representation admission.
"""
import argparse,hashlib,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store

def publish(reports,requests,target,directory,compilation=None):
    store=Store.publish(directory,[])
    candidates={}
    for report in reports:
        data=json.loads(Path(report).read_text())
        if data.get('schema')!=2 or data.get('instrumented',False):
            raise ValueError('selection requires ordinary uninstrumented whole-call timings')
        for row in data['measurements']:
            label=row['candidate'];raw=(requests/(label+'.json')).read_bytes();request=json.loads(raw)
            plan=hashlib.sha256(raw).hexdigest();source=request['input_core_sha256']
            candidates[label]=dict(request_sha256=plan,representation=request['representation'],source=source)
            workload=dict(shape=dict(rows=row['rows'],calls=row['calls_per_sample']),
                distribution=dict(query=row['query'],read_percent=row['read_percent'],script='bench/point-delta/standalone-aggregate.rs.txt'),
                concurrency=1,residency='restored; acknowledgement after every call')
            def observe(phase,samples):
                return store.observe(dict(schema=1,program=source,entries=[],plan=plan,target=target,
                    workload={**workload,'distribution':dict(workload=workload['distribution'],phase=phase)},
                    metrics=dict(complete_call_ns=[str(n)for n in samples],peak_bytes=None)))
            observe('action:batch_calls',[sample['native_ns']for sample in row['samples']])
            initial=[p['initialise_ns']for p in data['phases']if p['rows']==row['rows']and p['candidate']==label]
            if initial:observe('initialise',initial)
            if compilation:
                checks=[p['check_ns']for p in compilation if p.get('candidate')==label]
                if checks:observe('check',checks)
    store.rebuild()
    manifest=dict(schema=1,snapshot=store.snapshot_id,target=target,candidates=candidates,
        scope='measured whole batches; exact query/read mix and row/call counts only; portable migration and unmeasured memory require independent evidence')
    (directory/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return manifest

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('reports',type=Path,nargs='+');p.add_argument('--requests',type=Path,required=True);p.add_argument('--target',type=Path,required=True);p.add_argument('--compilation',type=Path);p.add_argument('-o','--output',type=Path,required=True);a=p.parse_args()
    print(json.dumps(publish(a.reports,a.requests,json.loads(a.target.read_text()),a.output,json.loads(a.compilation.read_text())if a.compilation else None)))
