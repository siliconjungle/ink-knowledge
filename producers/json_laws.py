#!/usr/bin/env python3
"""Publish generic JSON object-list laws through ordinary source law checking."""
import argparse,json,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from ink_knowledge import Store,canonical

def publish(compiler,output):
    output=Path(output)
    with tempfile.TemporaryDirectory(prefix='ink-json-laws-') as temporary:
        bundle_path=Path(temporary)/'bundle.json'
        checked=subprocess.run([str(compiler),'emit-laws',str(ROOT/'libraries/json-laws.ink'),'-o',str(bundle_path)],capture_output=True,text=True,timeout=60)
        if checked.returncode:raise ValueError('JSON law authoring rejected: '+checked.stderr.strip())
        receipt=json.loads(checked.stdout);bundle=json.loads(bundle_path.read_text())
    names={'rewrite/json/'+name:key for name,key in receipt['names'].items()}
    roots=list(bundle['roots'])
    if Store.is_published(output):
        previous=Store(output)
        rewrites=json.loads((output/'store/rewrite-view.json').read_text())['roots']
        store=previous.extend(list(bundle['objects'].values()),names)
    else:
        rewrites=[];store=Store.publish(output,list(bundle['objects'].values()),names)
    store.ensure_index()
    (output/'store/rewrite-view.json').write_bytes(canonical(store.bundle(sorted(set(rewrites+roots))))+b'\n')
    (output/'store/json-view.json').write_bytes(canonical(store.bundle(roots))+b'\n')
    return dict(laws=len(roots),snapshot=store.snapshot_id,names=receipt['names'])
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiler',type=Path,required=True)
    p.add_argument('--output-store',type=Path,required=True)
    a=p.parse_args();print(json.dumps(publish(a.compiler.resolve(),a.output_store)))
