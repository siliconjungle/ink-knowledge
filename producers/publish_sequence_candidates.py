#!/usr/bin/env python3
"""Publish sequence candidates with shared proof objects, preserving old pins.

Authoring only: the selector reconstructs an authenticated complete view and
replays the ordinary representation checker before any execution or emission.
"""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,identity
from ink_knowledge.store import read
from ink_knowledge.implementation_candidates import publish_candidates,identity_selection

def publish(root,request_paths):
    packages=[json.loads(p.read_text())for p in request_paths]
    sources={p['input_core_sha256']for p in packages}
    if len(sources)!=1:raise ValueError('candidate source mismatch')
    source=next(iter(sources));packages.insert(0,identity_selection(source))
    old=Store(root).snapshot_id
    store,ids=publish_candidates(root,packages,shared_knowledge=True)
    names={}
    labels=['ordinary-source',*[p.stem for p in request_paths]]
    names.update(('sequence-candidates/'+n,i)for n,i in zip(labels,ids))
    store=store.extend([],names);store.refresh_index()
    return dict(schema=1,source=source,previous_snapshot=old,snapshot=store.snapshot_id,
        candidates=dict(zip(labels,ids)),scope='shared content-addressed proof closures; every selected package requires ordinary complete checker replay')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('requests',type=Path,nargs='+');p.add_argument('--root',type=Path,required=True);p.add_argument('-o','--output',type=Path,required=True);a=p.parse_args()
    result=publish(a.root,a.requests);a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
