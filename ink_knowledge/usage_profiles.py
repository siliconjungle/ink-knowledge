"""Immutable observed usage cohorts. Discovery and aggregation are offline;
recorded shapes/frequencies never discharge an equality or resource-safety proof.
"""
import argparse,json,re
from pathlib import Path
from .store import Store,entry,identity,hash_id,canonical
SEMANTICS='ink-observed-usage-v1'

def validate(profile):
    keys={'schema','semantics','recording_id','source','target','workload','counts','peak_pending','peak_pending_bytes','failed','saturated','events','shapes'}
    if not isinstance(profile,dict) or set(profile)!=keys or profile['schema']!=1 or profile['semantics']!=SEMANTICS:raise ValueError('usage profile schema')
    if not isinstance(profile['recording_id'],str) or not re.fullmatch(r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}',profile['recording_id']):raise ValueError('usage recording identity')
    hash_id(profile['source'])
    Store.validate_observation(dict(schema=1,program=profile['source'],entries=[],plan=profile['source'],target=profile['target'],workload=profile['workload'],metrics=dict(complete_call_ns=['0'],peak_bytes=None)))
    counts=profile['counts']
    if not isinstance(counts,dict) or not 1<=len(counts)<=64 or any(not re.fullmatch(r'[A-Za-z0-9:_\-.]{1,128}',k) or type(v)is not int or not 0<=v<=1_000_000_000 for k,v in counts.items()) or not any(counts.values()):raise ValueError('usage counts')
    for field,limit in [('peak_pending',1_000_000),('peak_pending_bytes',9_007_199_254_740_991),('events',1_000_000_000),('failed',1_000_000_000)]:
        if type(profile[field])is not int or not 0<=profile[field]<=limit:raise ValueError('usage '+field)
    if type(profile['saturated'])is not bool or profile['events']<sum(counts.values()) or profile['failed']>sum(counts.values()):raise ValueError('usage event accounting')
    if not isinstance(profile['shapes'],list) or len(profile['shapes'])>256:raise ValueError('usage shape budget')
    seen=set()
    for shape in profile['shapes']:
        if not isinstance(shape,dict) or set(shape)!={'shape','count'} or not isinstance(shape['shape'],list) or len(shape['shape'])!=3:raise ValueError('usage shape schema')
        function,elements,size=shape['shape']
        if function is not None and (not isinstance(function,str) or len(function)>128):raise ValueError('usage function')
        if any(type(v)is not int or not 0<=v<=9_007_199_254_740_991 for v in (elements,size)) or type(shape['count'])is not int or not 1<=shape['count']<=1_000_000_000:raise ValueError('usage shape count')
        key=canonical(shape['shape'])
        if key in seen:raise ValueError('duplicate usage shape')
        seen.add(key)
    if sum(s['count'] for s in profile['shapes'])>sum(counts.values()):raise ValueError('usage shape accounting')
    return profile

def publish(store,profile):
    validate(profile)
    obj=entry('definition',SEMANTICS,profile)
    return store.extend([obj],{'usage/'+identity(obj):identity(obj)})

def discover(store,source,backend):
    """Page all recordings. Cumulative snapshots of a recording supersede earlier
    snapshots; independent windows have distinct IDs and contribute independently.
    Target/distribution cohorts never borrow one another's cost measurements.
    """
    recordings={};after=None
    while True:
        page=store.query(kind='definition',semantics=SEMANTICS,after=after,limit=256)
        for ident in page:
            profile=validate(store.object(ident)['payload'])
            if profile['source']!=source or profile['target']['backend']!=backend:continue
            rid=profile['recording_id'];previous=recordings.get(rid)
            if previous:
                old=previous[1]
                if (old['target'],old['workload'])!=(profile['target'],profile['workload']):
                    # Automatically derived cumulative distributions evolve with
                    # the recording. Explicit cohorts must remain stable.
                    auto=lambda p:isinstance(p['workload']['distribution'],dict) and 'recorded_frequencies' in p['workload']['distribution']
                    if old['target']!=profile['target'] or not(auto(old) and auto(profile)):raise ValueError('recording changed its cohort binding')
                if old['events']==profile['events'] and canonical({k:v for k,v in old.items() if k!='saturated'})!=canonical({k:v for k,v in profile.items() if k!='saturated'}):raise ValueError('ambiguous cumulative usage snapshot')
                older,newer=sorted([old,profile],key=lambda p:(p['events'],p['saturated']))
                if any(v>newer['counts'].get(k,0) for k,v in older['counts'].items()) or any(older[k]>newer[k] for k in ['peak_pending','peak_pending_bytes','failed']):raise ValueError('conflicting cumulative usage snapshots')
                if newer is old:continue
            recordings[rid]=(ident,profile)
        if len(page)<256:break
        after=page[-1]
    groups={}
    for ident,profile in recordings.values():
        key=identity(dict(target=profile['target'],workload=profile['workload']))
        group=groups.setdefault(key,dict(source=source,target=profile['target'],workload=profile['workload'],counts={},peak_pending=0,peak_pending_bytes=0,evidence=[],saturated=False))
        for phase,count in profile['counts'].items():
            group['counts'][phase]=group['counts'].get(phase,0)+count
            if group['counts'][phase]>1_000_000_000 or len(group['counts'])>64:raise ValueError('aggregated usage count budget')
        for field in ['peak_pending','peak_pending_bytes']:group[field]=max(group[field],profile[field])
        group['evidence'].append(ident);group['saturated']|=profile['saturated']
    for group in groups.values():group['evidence'].sort()
    return [groups[k] for k in sorted(groups)]

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--knowledge-root',type=Path,required=True);p.add_argument('--recording',type=Path,required=True);a=p.parse_args()
    store=publish(Store(a.knowledge_root),json.loads(a.recording.read_bytes()))
    print(json.dumps(dict(snapshot=store.snapshot_id,scope='observed usage; no proof authority')))
if __name__=='__main__':main()
