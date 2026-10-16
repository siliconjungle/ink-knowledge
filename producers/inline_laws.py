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
        # A call evaluates every argument once, in declaration order, before
        # its body. Preserve that complete interface even for unused formals,
        # lazy bodies and repeated non-scalar values. Existing lambda/apply
        # syntax reifies to typed lexical lets; no carrier whitelist or target
        # shortcut supplies equality or profitable-selection authority.
        target=shared_arguments(body,list(params.items()))
        try:proposal=bind(law(params,source,target),core,subject,[f['name']])
        except(ValueError,KeyError):continue
        rows.append(('unfold_'+f['name'],proposal))
    return rows

def shared_arguments(body, parameters):
    """Bind call arguments in order before entering an unfolded body.

    The lambda/apply form reifies to ordinary lexical lets. Beta normalization
    proves the same value; it grants no unchecked access or mutation authority.
    Free formal references become bound references under existing callbacks.
    """
    from producers.semantic_laws import bound,lam
    names={name:(len(parameters)-1-i,sort) for i,(name,sort) in enumerate(parameters)}
    def abstract(term,depth=0):
        node=term['node']
        if isinstance(node,dict) and 'Free' in node and node['Free'] in names:
            index,sort=names[node['Free']]
            return bound(sort,index+depth)
        if isinstance(node,dict) and 'Lambda' in node:
            return dict(term,node={'Lambda':abstract(node['Lambda'],depth+1)})
        if isinstance(node,dict) and 'Cons' in node:
            return dict(term,node={'Cons':[abstract(arg,depth)for arg in node['Cons']]})
        if isinstance(node,dict) and 'Op' in node:
            name,args=node['Op']
            return dict(term,node={'Op':[name,[abstract(arg,depth)for arg in args]]})
        return term
    target=abstract(body)
    for _,sort in reversed(parameters):target=lam(sort,target)
    for name,sort in parameters:target=op(target['sort']['Arrow'][1],'apply',target,var(sort,name))
    return target
