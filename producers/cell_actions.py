"""Propose one upsert for a guarded replace/insert; prove the whole action."""
import copy,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import canonical
from producers.action_replacement import produce

def candidates(context):
    if context.get('representation')or context.get('maintained'):return
    core=context['core'];count=0
    def sites(block,path):
        for i,s in enumerate(block):
            if 'If'not in s:continue
            condition,a,b=s['If'];method=condition.get('Method')if isinstance(condition,dict)else None
            if method and method[1]=='contains'and len(method[2])==1 and len(a)==len(b)==1:
                x=a[0].get('Expr',{}).get('Method');y=b[0].get('Expr',{}).get('Method')
                if x and y and x[0]==y[0]==method[0]and x[1]=='replace'and y[1]=='insert'and x[2]==y[2]and len(x[2])==2 and x[2][0]==method[2][0]:
                    yield path+[i],{'Expr':{'Method':[x[0],'put',x[2]]}}
            yield from sites(a,path+[i,'If',1]);yield from sites(b,path+[i,'If',2])
    for index,action in enumerate(core['program'].get('actions',[])):
        for path,replacement in sites(action['body'],['program','actions',index,'body']):
            count+=1
            if count>32:return
            selected=copy.deepcopy(core);parent=selected
            for part in path[:-1]:parent=parent[part]
            parent[path[-1]]=replacement
            try:
                with tempfile.TemporaryDirectory(prefix='ink-cell-action-')as temporary:
                    d=Path(temporary);source=d/'selected.json';source.write_bytes(canonical(selected));model=d/'model.json'
                    result=subprocess.run([context['compiler'],'emit-action-model',str(source),'--core','-o',str(model)],capture_output=True,text=True,timeout=120)
                    if result.returncode:raise ValueError(result.stderr.strip())
                    package=produce(context['model'],json.loads(model.read_bytes()),selected,d/'knowledge',context['knowledge_root'])
                    yield dict(status='proposal',label='single-upsert/'+action['name'],steps=[dict(kind='rewrite',package=package)])
            except(ValueError,KeyError,subprocess.TimeoutExpired)as error:
                yield dict(status='declined',label='single-upsert/'+action['name'],reason=str(error))
