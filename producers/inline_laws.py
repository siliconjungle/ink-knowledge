"""Untrusted, universally replayable definition unfolding choices."""
from producers.semantic_laws import value,var,op,law
from producers.definition_context28 import bind

def specialize(subject,core):
    from ink_planner.semantic_search import children
    def size(t):return 1+sum(size(c)for c in children(t))
    rows=[]
    for f in core['program']['functions'][:256]:
        body=subject['functions'].get(f['name'])
        if body is None or size(body)>2048:continue
        params={n:value(t)for n,t in f['params']}
        source=op(value(f['result']),'call:'+f['name'],*(var(params[n],n)for n,_ in f['params']))
        try:proposal=bind(law(params,source,body),core,subject,[f['name']])
        except(ValueError,KeyError):continue
        rows.append(('unfold_'+f['name'],proposal))
    return rows
