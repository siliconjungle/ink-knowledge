"""Propose earlier parameter-dependent returns; check whole-action equality.

Syntactic eligibility only proposes a move. Complete observations (result, error,
state, commitment and events) must agree for arbitrary initial state. Earlier
failures or reads that matter therefore reject the move through ordinary proofs.
"""
import argparse,copy,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import canonical
from producers.action_replacement import produce

def candidates(context):
    if context.get('representation')or context.get('maintained'):
        return
    core=context['core'];attempts=0
    def names(value):
        if isinstance(value,dict):
            if set(value)=={'Var'}:yield value['Var']
            for v in value.values():yield from names(v)
        elif isinstance(value,list):
            for v in value:yield from names(v)
    for index,action in enumerate(core['program'].get('actions',[])):
        params={n for n,_ in action['params']}|set(core['program'].get('enums',{}))
        for at,statement in enumerate(action['body']):
            if at==0 or 'If'not in statement:continue
            condition,a,b=statement['If']
            if set(names(condition))-params:continue
            if not ((len(a)==1 and 'Return'in a[0]and not b)or(len(b)==1 and 'Return'in b[0]and not a)):continue
            if set(names(a or b))-params:continue
            attempts+=1
            if attempts>32:return
            selected=copy.deepcopy(core);body=selected['program']['actions'][index]['body'];body.insert(0,body.pop(at))
            try:
                with tempfile.TemporaryDirectory(prefix='ink-early-return-')as temporary:
                    d=Path(temporary);source=d/'selected.json';source.write_bytes(canonical(selected))
                    model=d/'model.json'
                    result=subprocess.run([context['compiler'],'emit-action-model',str(source),'--core','-o',str(model)],capture_output=True,text=True,timeout=120)
                    if result.returncode:raise ValueError(result.stderr.strip())
                    package=produce(context['model'],json.loads(model.read_bytes()),selected,d/'knowledge',context['knowledge_root'])
                    yield dict(status='proposal',label='early-return/'+action['name']+'/'+str(at),steps=[dict(kind='rewrite',package=package)])
            except (ValueError,KeyError,subprocess.TimeoutExpired)as error:
                yield dict(status='declined',label='early-return/'+action['name'],reason=str(error))

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source',type=Path);p.add_argument('--compiler',type=Path,required=True);p.add_argument('--knowledge-root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('-o',type=Path,required=True);a=p.parse_args()
    a.o.mkdir(parents=True,exist_ok=True)
    core=a.o/'core.json';model=a.o/'model.json'
    for command,out in [('emit-core',core),('emit-action-model',model)]:
        subprocess.run([str(a.compiler.resolve()),command,str(a.source),'-o',str(out)],check=True)
    context=dict(core=json.loads(core.read_bytes()),model=json.loads(model.read_bytes()),compiler=str(a.compiler.resolve()),knowledge_root=str(a.knowledge_root.resolve()))
    rows=list(candidates(context));(a.o/'proposals.json').write_bytes(canonical(rows))
    print(json.dumps([dict(label=r['label'],status=r['status'])for r in rows]))
if __name__=='__main__':main()
