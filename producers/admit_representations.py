#!/usr/bin/env python3
"""Publish exact source-bound candidates only after local admission of all plans.

Usage: admit_representations.py KNOWLEDGE --compiler INK --report RECEIPT
       --candidate NAME SOURCE REQUEST [--candidate ...]
       [--mathematics NAME CORE VIEW]
Canonical objects are immutable; failed checking never changes the active pin.
"""
import argparse,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store

def publish(root,compiler,candidates,report,mathematics=()):
    root=Path(root).resolve();compiler=Path(compiler).resolve()
    digest=lambda:hashlib.sha256(compiler.read_bytes()).hexdigest()
    before_hash=digest();original=Store(root);members=set(original.members())
    objects={i:original.object(i)for i in members};names=original.names;subjects=[]
    for name,source,path in candidates:
        request=json.loads(Path(path).read_text());source=Path(source).resolve()
        for i,e in request['knowledge']['objects'].items():
            if i in objects and objects[i]!=e:raise ValueError('conflicting canonical object')
            objects[i]=e
        names['composable-representations/'+name]=request['representation'];subjects.append((name,source,request))
    math_subjects=[]
    for name,core,path in mathematics:
        view=json.loads(Path(path).read_text())
        for i,e in view['objects'].items():
            if i in objects and objects[i]!=e:raise ValueError('conflicting canonical object')
            objects[i]=e
        for number,rid in enumerate(view['roots']):names[f'composable-mathematics/{name}/{number}']=rid
        math_subjects.append((name,Path(core).resolve(),view['roots']))
    with tempfile.TemporaryDirectory(prefix='ink-representation-admission-')as temp:
        stage=Store.publish(Path(temp),objects.values(),names);receipts=[]
        for number,(name,source,request)in enumerate(subjects):
            request={**request,'knowledge':stage.bundle([request['representation']])}
            path=Path(temp)/f'request-{number}.json';path.write_text(json.dumps(request))
            checked=subprocess.run([str(compiler),'check-representation',str(source),str(path)],capture_output=True,text=True)
            if checked.returncode:raise RuntimeError(checked.stderr.strip())
            result=json.loads(checked.stdout)
            if result['status']!='checked':raise RuntimeError('missing admission')
            receipts.append(dict(name=name,source=request['input_core_sha256'],representation=request['representation'],source_file_sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
        math_receipts=[]
        for number,(name,core,roots)in enumerate(math_subjects):
            path=Path(temp)/f'mathematics-{number}.json';path.write_text(json.dumps(stage.bundle(roots)))
            checked=subprocess.run([str(compiler),'knowledge-check',str(core),str(path)],capture_output=True,text=True)
            if checked.returncode:raise RuntimeError(checked.stderr.strip())
            result=json.loads(checked.stdout)
            if result['status']!='checked':raise RuntimeError('missing mathematics admission')
            math_receipts.append(dict(name=name,roots=roots,core_file_sha256=hashlib.sha256(core.read_bytes()).hexdigest()))
        if digest()!=before_hash:raise RuntimeError('compiler changed during admission')
        final=Store.publish(root,objects.values(),names)
        if final.snapshot_id!=stage.snapshot_id:raise RuntimeError('published bytes differ from admitted bytes')
        final.rebuild()
    historical=Store(root,root/'store/snapshots'/f'{original.snapshot_id}.json')
    if set(historical.members())!=members:raise RuntimeError('previous immutable pin changed')
    receipt=dict(schema=1,status='checked',previous_snapshot=original.snapshot_id,snapshot=final.snapshot_id,compiler_sha256=before_hash,added_entries=len(set(objects)-members),candidates=receipts,mathematics=math_receipts,scope='Representation admission checks complete source observations and universal state relations. Mathematical roots are checked separately. Profitability requires comparable lifecycle evidence.')
    Path(report).parent.mkdir(parents=True,exist_ok=True);Path(report).write_text(json.dumps(receipt,indent=2)+'\n');return receipt

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('knowledge',type=Path);parser.add_argument('--compiler',type=Path,required=True);parser.add_argument('--report',type=Path,required=True);parser.add_argument('--candidate',action='append',nargs=3,metavar=('NAME','SOURCE','REQUEST'),default=[]);parser.add_argument('--mathematics',action='append',nargs=3,metavar=('NAME','CORE','VIEW'),default=[])
    a=parser.parse_args();receipt=publish(a.knowledge,a.compiler,a.candidate,a.report,a.mathematics);print(json.dumps(dict(status=receipt['status'],snapshot=receipt['snapshot'],candidates=len(receipt['candidates']))))
if __name__=='__main__':main()
