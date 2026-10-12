"""Propose exact postcondition witnesses; replay before publishing candidates.

Search policy lives here, outside the compiler. A result equality supplies an
obvious witness, but every remaining clause, invariant and caller is rechecked.
"""
import argparse,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge.implementation_candidates import identity_selection,publish_candidates
from .contract_proofs import author

def propose(compiler,source,output,source_evidence=None):
    compiler=str(Path(compiler).resolve());source=str(Path(source).resolve());out=Path(output).resolve();out.mkdir(parents=True,exist_ok=True)
    core_input=Path(source).suffix=='.json'
    if source_evidence is None and not core_input:
        author(compiler,source,out/'baseline-proofs');source_evidence=out/'baseline-proofs/evidence.json'
    core=out/'input-core.json'
    receipt=json.loads(subprocess.check_output([compiler,'emit-core',source,*(['--core'] if core_input else []),*(['--contract-proofs',str(source_evidence)] if source_evidence else []),'-o',str(core)],text=True))
    original=identity_selection(receipt['core_sha256']);program=json.loads(core.read_text())['program'];packages=[original];rejected=[]
    for spec in program.get('contracts',{}).get('specifications',[]):
        if spec['kind'] is not None:continue
        for clause in spec['ensures']:
            eq=clause.get('Binary')
            if not eq or eq[0]!='==':continue
            if eq[1]=={'Var':'result'}:body=eq[2]
            elif eq[2]=={'Var':'result'}:body=eq[1]
            else:continue
            # Capturing result would create an ill-scoped proposal; the checker
            # rejects it too, but do not waste a proof search on that shape.
            def mentions(x):
                if x=={'Var':'result'}:return True
                if isinstance(x,dict):return any(mentions(v) for v in x.values())
                if isinstance(x,list):return any(mentions(v) for v in x)
                return False
            if mentions(body):continue
            directory=out/f'proposal-{len(packages)}';directory.mkdir(parents=True,exist_ok=True)
            bodies={spec['name']:{'Pure':body}};path=directory/'bodies.json';path.write_text(json.dumps(bodies))
            try:
                evidence,_=author(compiler,core,directory/'proofs',path)
                package={**original,'contract_refinement':dict(bodies=bodies,evidence=evidence)}
                trial=directory/'selection.json';trial.write_text(json.dumps(package))
                subprocess.run([compiler,'check-selection',str(core),str(trial)],capture_output=True,text=True,check=True)
                packages.append(package)
            except (ValueError,subprocess.CalledProcessError) as error:rejected.append(dict(specification=spec['name'],reason=str(error)))
    store,ids=publish_candidates(out,packages)
    report=dict(schema=1,semantics='ink-contract-candidates-v1',source=receipt['core_sha256'],snapshot=store.snapshot_id,baseline=ids[0],candidates=ids[1:],rejected=rejected)
    (out/'candidates.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source');p.add_argument('output');p.add_argument('--compiler',required=True);p.add_argument('--source-evidence');a=p.parse_args();print(json.dumps(propose(a.compiler,a.source,a.output,a.source_evidence)))
if __name__=='__main__':main()
