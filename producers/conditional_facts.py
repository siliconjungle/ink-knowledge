"""Offline discovery of source equalities from untrusted word facts.

Every whole-function proposal is independently checked before publication.
Acquisition does not select a profitable implementation or change runtime policy.
"""
import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time
from ink_knowledge import Store, canonical, identity, semantic_entry
from .word_facts import analyse_candidates
from .beta_specialization15 import free_parameters
from .author_word_identities import checked_law, update_frozen_data
from .workspace import compiler_path
from .call_facts import expand
from .definition_context28 import bind


def acquire(source, compiler, directory, *, store_root=None, frozen=None, seconds=5):
    source, compiler, directory = Path(source).resolve(), Path(compiler).resolve(), Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    if (directory/'receipt.json').exists():raise ValueError('Choose a fresh acquisition directory')
    source_hash=hashlib.sha256(source.read_bytes()).hexdigest()
    compiler_hash=hashlib.sha256(compiler.read_bytes()).hexdigest()
    core, subject = directory/'core.json', directory/'subject.json'
    for args in [('emit-core',source,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
        result=subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=120)
        if result.returncode:raise ValueError(result.stderr[-4000:])
    model=json.loads(subject.read_bytes());executable=json.loads(core.read_bytes());objects={};applications=[];attempts=[];rows=[]
    if len(model['functions'])>256:raise ValueError('Fact acquisition function limit')
    for function, original in sorted(model['functions'].items()):
        started=time.monotonic_ns()
        summary=None;analysed=original
        try:
            analysed,summary=expand(original,executable,model)
            facts, proposals=analyse_candidates(analysed)
        except ValueError as error:
            attempts.append(dict(function=function,status='unknown',reason=str(error)));continue
        if not proposals:
            attempts.append(dict(function=function,status='no-candidate',facts=asdict(facts),call_summary=summary));continue
        seen=set()
        for label,candidate in proposals[:4]:
            key=identity(candidate)
            if key in seen:continue
            seen.add(key)
            with tempfile.TemporaryDirectory(prefix='ink-conditional-facts-')as tmp:
                try:
                    params=free_parameters(original)
                    scalar_law,proof=checked_law(compiler,core,dict(params=params,conditions=[],**{'from':analysed,'to':candidate}),Path(tmp),seconds=seconds)
                    law=scalar_law
                    if analysed!=original:
                        law=bind(dict(scalar_law,**{'from':original,'proof':{'Trans':dict(middle=analysed,left='Normalize',right=scalar_law['proof'])}}),executable,model)
                        object_=semantic_entry(law);local_view=Store.publish(Path(tmp)/'whole-call',[object_]);view=Path(tmp)/'whole-call.json';view.write_bytes(canonical(local_view.bundle([identity(object_)])))
                        check=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],capture_output=True,text=True,timeout=120)
                        if check.returncode:raise ValueError(check.stderr[-4000:])
                except (ValueError,subprocess.TimeoutExpired)as error:
                    attempts.append(dict(function=function,label=label,status='unproved',reason=str(error)));continue
            obj=semantic_entry(law);ident=identity(obj);objects[ident]=obj
            # One application per root; all independently checked alternatives
            # remain reusable laws, not repeated applications to a changed root.
            if not any(a['function']==function for a in applications):
                applications.append(dict(function=function,path=[],law=ident,
                    arguments={n:dict(sort=s,node={'Free':n})for n,s in params.items()},premises=[]))
            rows.append(dict(name='conditional-facts/'+ident,law=law))
            attempts.append(dict(function=function,label=label,status='checked',law=ident,
                facts=asdict(facts),call_summary=summary,proof=proof,elapsed_ns=time.monotonic_ns()-started))
    if hashlib.sha256(source.read_bytes()).hexdigest()!=source_hash or hashlib.sha256(compiler.read_bytes()).hexdigest()!=compiler_hash:
        raise ValueError('Acquisition input changed')
    # Check the complete packet before publishing into an installed database.
    local=Store.publish(directory/'knowledge',objects.values())
    packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=model['input_core_sha256'],
        knowledge=local.bundle(sorted(objects)),applications=applications)
    selection=directory/'selection.json';selection.write_bytes(canonical(packet))
    result=subprocess.run([str(compiler),'check-selection',str(core),str(selection)],capture_output=True,text=True,timeout=120)
    if result.returncode:raise ValueError(result.stderr[-4000:])
    snapshot=None
    if store_root is not None:
        store=Store(store_root).extend(objects.values(),{row['name']:identity(semantic_entry(row['law']))for row in rows}) if Store.is_published(store_root)else Store.publish(store_root,objects.values())
        snapshot=store.snapshot_id
    if frozen is not None:update_frozen_data(frozen,rows)
    receipt=dict(schema=1,source_sha256=source_hash,compiler_sha256=compiler_hash,
        input_core_sha256=model['input_core_sha256'],snapshot=snapshot,attempts=attempts,
        checked_laws=len(objects),applications=len(applications),
        authority='Every law and the complete selection replayed by Ink; profitability unmeasured')
    (directory/'receipt.json').write_bytes(canonical(receipt)+b'\n')
    return packet,receipt


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path);parser.add_argument('-o',type=Path,required=True)
    parser.add_argument('--compiler',type=Path,default=compiler_path())
    parser.add_argument('--output-store',type=Path);parser.add_argument('--frozen',type=Path)
    parser.add_argument('--seconds',type=int,default=5)
    args=parser.parse_args()
    if not 1<=args.seconds<=120:parser.error('seconds must be in 1..120')
    _,receipt=acquire(args.source,args.compiler,args.o,store_root=args.output_store,frozen=args.frozen,seconds=args.seconds)
    print(json.dumps(dict(checked_laws=receipt['checked_laws'],applications=receipt['applications'],snapshot=receipt['snapshot'])))


if __name__=='__main__':main()
