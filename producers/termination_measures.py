"""Untrusted decreasing-measure authoring; every call certificate replays in Ink."""
import argparse,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import Store,identity,canonical
from ink_knowledge.store import entry
from producers.physical_capabilities import bit_proof,invoke,write

SEMANTICS='ink-source-termination-v1'
def produce(source,compiler,directory):
    source=Path(source).resolve();compiler=Path(compiler).resolve()
    directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='ink-termination-') as temporary:
        scratch=Path(temporary);export=scratch/'goals.json'
        invoke(compiler,'emit-termination-obligations',source,'-o',export)
        goals=json.loads(export.read_bytes());objects=[];names={}
        for goal in goals['obligations']:
            proof=bit_proof(compiler,scratch,{k:goal[k]for k in ('params','conditions','from','to')})
            obj=entry('definition',SEMANTICS,dict(source=goals['source'],site=goal['site'],obligation_sha256=identity(goal),proof=proof))
            objects.append(obj);names[goal['site']['function']+'/'+'.'.join(map(str,goal['site']['path']))]=identity(obj)
        store=Store.publish(directory,objects,names)
        bundle=store.bundle(list(names.values()))
        evidence=write(directory/'evidence.json',bundle)
        # A false, stale or incomplete certificate can never become a success
        # receipt merely because the solver or canonical publication returned.
        invoke(compiler,'check-termination',source,'--termination-proofs',evidence)
        write(directory/'obligations.json',goals)
        write(directory/'production.json',dict(schema=1,source=goals['source'],calls=len(names),snapshot=store.snapshot_id))
        return bundle,store
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source');parser.add_argument('output');parser.add_argument('--compiler',required=True)
    args=parser.parse_args();produce(args.source,args.compiler,args.output)
    print('Checked every recursive call:',args.output)
if __name__=='__main__':main()
