"""Propose bounded witnesses for source contracts; replay before publication.

Search policy lives here, outside the compiler. A result equality supplies an
obvious witness, but every remaining clause, invariant and caller is rechecked.
"""
import argparse,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge.implementation_candidates import identity_selection,publish_candidates
from .contract_proofs import author
from .contract_search import witnesses,key

def propose(compiler,source,output,source_evidence=None,*,max_per_spec=32,max_proposals=256):
    if not 1<=max_per_spec<=256 or not 1<=max_proposals<=4096:raise ValueError('contract candidate budget')
    compiler=str(Path(compiler).resolve());source=str(Path(source).resolve());out=Path(output).resolve();out.mkdir(parents=True,exist_ok=True)
    core_input=Path(source).suffix=='.json'
    if source_evidence is None and not core_input:
        author(compiler,source,out/'baseline-proofs');source_evidence=out/'baseline-proofs/evidence.json'
    core=out/'input-core.json'
    receipt=json.loads(subprocess.check_output([compiler,'emit-core',source,*(['--core'] if core_input else []),*(['--contract-proofs',str(source_evidence)] if source_evidence else []),'-o',str(core)],text=True))
    original=identity_selection(receipt['core_sha256']);program=json.loads(core.read_text())['program'];packages=[original];rejected=[];attempts=0;seen=set()
    for spec in program.get('contracts',{}).get('specifications',[]):
        current=next(({'Pure':f['body']}for f in program.get('functions',[])if f['name']==spec['name']),None)if spec['kind']is None else next(({'Action':a['body']}for a in program.get('actions',[])if a['name']==spec['name']),None)
        for body in witnesses(program,spec,max_per_spec):
            if body==current:continue
            bodies={spec['name']:body};fingerprint=key(bodies)
            if fingerprint in seen:continue
            if attempts>=max_proposals:break
            seen.add(fingerprint);attempts+=1
            directory=out/f'proposal-{attempts}';directory.mkdir(parents=True,exist_ok=True)
            path=directory/'bodies.json';path.write_text(json.dumps(bodies))
            try:
                evidence,_=author(compiler,core,directory/'proofs',path)
                package={**original,'contract_refinement':dict(bodies=bodies,evidence=evidence)}
                trial=directory/'selection.json';trial.write_text(json.dumps(package))
                subprocess.run([compiler,'check-selection',str(core),str(trial)],capture_output=True,text=True,check=True)
                packages.append(package)
            except (ValueError,subprocess.CalledProcessError) as error:rejected.append(dict(specification=spec['name'],body=body,reason=str(error)))
    store,ids=publish_candidates(out,packages)
    report=dict(schema=1,semantics='ink-contract-candidates-v1',source=receipt['core_sha256'],snapshot=store.snapshot_id,baseline=ids[0],candidates=ids[1:],rejected=rejected,attempts=attempts,budget=dict(per_spec=max_per_spec,proposals=max_proposals),exhausted=attempts>=max_proposals)
    (out/'candidates.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source');p.add_argument('output');p.add_argument('--compiler',required=True);p.add_argument('--source-evidence');p.add_argument('--max-per-spec',type=int,default=32);p.add_argument('--max-proposals',type=int,default=256);a=p.parse_args();print(json.dumps(propose(a.compiler,a.source,a.output,a.source_evidence,max_per_spec=a.max_per_spec,max_proposals=a.max_proposals)))
if __name__=='__main__':main()
