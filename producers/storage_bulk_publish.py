#!/usr/bin/env python3
"""Publish checked bulk laws and replayable storage/reducer fixture candidates.

Publication is untrusted; the supplied compiler checks every mathematical view
and every complete source-bound representation before the pointer is updated.
"""
import argparse, json, subprocess, sys, tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, identity, semantic_entry, canonical
from ink_knowledge.store import read, entry
from producers.bulk_collection_laws import named_laws
from producers.packed_representations import generate as packed
from producers.representations import generate as cached


def publish(root, source_root, compiler):
    root,source_root,compiler=Path(root).resolve(),Path(source_root).resolve(),Path(compiler).resolve()
    previous=Store(root);objects={i:previous.object(i) for i in previous.members()};names=read(previous.data/'names.json')
    laws=[]
    for name,law in named_laws():
        obj=semantic_entry(law);i=identity(obj);objects[i]=obj;names['rewrite/'+name]=i;laws.append(i)
    scalar=read(Path(__file__).parent/'data/word-equality.json');body=scalar['Theorem']
    obj=entry('theorem','first-order-inductive-equality-v1',dict(declaration=scalar),parameters=dict(body['params']),conditions=body['conditions'])
    equality=identity(obj);objects[equality]=obj;names['math/word-equality-extraction']=equality
    requests={};layouts={}
    with tempfile.TemporaryDirectory(prefix='ink-storage-publication-') as temporary:
        tmp=Path(temporary)
        def model(source,name):
            path=tmp/(name+'.json')
            subprocess.run([str(compiler),'emit-action-model',str(source),'-o',str(path)],check=True,capture_output=True)
            return read(path)
        table_source=source_root/'examples/action-transitions.ink';table=model(table_source,'tables')
        direct=cached(table,tmp/'direct')['requests'][0];requests['direct']=(table_source,direct)
        for width in [2,4]:
            for keys,label in [((),'packed-'+str(width)),((0,),'indexed-'+str(width)+'-hot-0')]:
                result=packed(table,tmp/label,width,keys,compiler);requests[label]=(table_source,result['request']);layouts[label]=result['layouts']
        label='indexed-4-hot-1023'
        result=packed(table,tmp/label,4,(1023,),compiler);requests[label]=(table_source,result['request']);layouts[label]=result['layouts']
        boolean_source=source_root/'examples/boolean-aggregates.ink';boolean=model(boolean_source,'booleans')
        requests['boolean-direct']=(boolean_source,cached(boolean,tmp/'boolean-direct')['requests'][0])
        for query,label in [('any_query','any-delta'),('all_query','all-delta')]:
            result=cached(boolean,tmp/label,cache_query=query,preserve_cache=True,compact_queries=True,aggregate_query=True)
            requests[label]=(boolean_source,result['requests'][1])
        for label,(source,request) in requests.items():
            path=tmp/(label+'.request.json');path.write_bytes(canonical(request)+b'\n')
            subprocess.run([str(compiler),'check-representation',str(source),str(path)],check=True,capture_output=True)
            objects.update(request['knowledge']['objects']);names['representations/storage-bulk/'+label]=request['representation']
        # Check new general laws before publishing the full snapshot too.
        subset=Store.publish(tmp/'general', [objects[i] for i in [*laws,equality]])
        view=tmp/'general.json';view.write_bytes(canonical(subset.bundle([*laws,equality]))+b'\n')
        core=tmp/'core.json';subprocess.run([str(compiler),'emit-core',str(table_source),'-o',str(core)],check=True,capture_output=True)
        subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],check=True,capture_output=True)
    store=Store.publish(root,objects.values(),names);added=store.refresh_index()
    destination=root/'research/storage-bulk';destination.mkdir(parents=True,exist_ok=True)
    (destination/'app.ink').write_bytes(table_source.read_bytes());(destination/'booleans.ink').write_bytes(boolean_source.read_bytes())
    (destination/'layouts.json').write_bytes(canonical(layouts)+b'\n')
    for label,(_,request) in requests.items():
        request['knowledge']=store.bundle([request['representation']])
        (destination/(label+'.json')).write_bytes(canonical(request)+b'\n')
    (store.data/'bulk-collection-view.json').write_bytes(canonical(store.bundle(laws))+b'\n')
    return dict(snapshot=store.snapshot_id,entries=len(store.members()),indexed_new=added,bulk_laws=len(laws),candidates=sorted(requests))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-store',type=Path,required=True);p.add_argument('--source-root',type=Path,required=True);p.add_argument('--compiler',type=Path,required=True)
    a=p.parse_args();print(json.dumps(publish(a.output_store,a.source_root,a.compiler)))
