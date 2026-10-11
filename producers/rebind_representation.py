#!/usr/bin/env python3
"""Rebind an archived request only when every fixed source entry is unchanged.

The compiler still rechecks the complete representation. This tool is authoring,
not admission, and never changes a proof or a source definition.
"""
import argparse,copy,json,subprocess,tempfile
from pathlib import Path

def rebind(request,model):
    result=copy.deepcopy(request);objects=model['objects'];plan=result['knowledge']['objects'][result['representation']]['payload']
    if plan['source_objects']!=sorted(objects):raise ValueError('fixed source definition set changed; regenerate proofs')
    for key,value in objects.items():
        if result['knowledge']['objects'].get(key)!=value:raise ValueError('fixed source bytes changed; regenerate proofs: '+key)
    result['input_core_sha256']=model['source']
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source',type=Path);p.add_argument('request',type=Path);p.add_argument('-o','--output',type=Path,required=True);p.add_argument('--compiler',type=Path,required=True);a=p.parse_args()
    compiler=a.compiler.resolve()
    with tempfile.TemporaryDirectory(prefix='ink-rebind-')as directory:
        d=Path(directory);model=d/'model.json';out=d/'request.json'
        subprocess.run([str(compiler),'emit-action-model',str(a.source),'-o',str(model)],check=True,capture_output=True)
        request=rebind(json.loads(a.request.read_text()),json.loads(model.read_text()))
        out.write_text(json.dumps(request,separators=(',',':'))+'\n')
        result=subprocess.run([str(compiler),'check-representation',str(a.source),str(out)],capture_output=True,text=True)
        if result.returncode:raise ValueError(result.stderr)
        a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(out.read_bytes())
        a.output.with_suffix(a.output.suffix+'.receipt.json').write_text(json.dumps(dict(old_source=json.loads(a.request.read_text())['input_core_sha256'],new_source=request['input_core_sha256'],fixed_source_objects=len(request['knowledge']['objects'][request['representation']]['payload']['source_objects']),full_check=json.loads(result.stdout)),indent=2)+'\n')
