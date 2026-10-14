"""Bounded untrusted exposure of leading lexical bindings for template search.

Only immediate lambda applications are reduced. The original source endpoint
is retained by callers and still needs the kernel's independent Normalize proof.
"""
def contexts(term, budget=None, limit=20_000):
    """Bounded enclosing contexts; never cross a lexical binder.

    These paths refer to the reduced search view, not to executable source.
    Callers must lift a proof back to the complete original expression.
    """
    from ink_planner.semantic_search import children
    shared=budget if budget is not None else [limit]
    remaining=limit
    def visit(value,path):
        nonlocal remaining
        remaining-=1;shared[0]-=1
        if remaining<0 or shared[0]<0:raise ValueError('template context budget')
        if len(path)>128:raise ValueError('template context depth')
        yield path,value
        node=value['node']
        if isinstance(node,dict)and 'Lambda'in node:return
        for i,child in enumerate(children(value)):
            yield from visit(child,path+(i,))
    yield from visit(term,())

def reduce(term, budget=None, limit=20_000):
    from ink_planner.semantic_search import map_children
    shared=budget if budget is not None else [limit]
    remaining=limit
    def spend(depth):
        nonlocal remaining
        remaining-=1;shared[0]-=1
        if remaining<0 or shared[0]<0:raise ValueError('template head reduction budget')
        if depth>128:raise ValueError('template head reduction depth')
    def shift(value,amount,local=0,depth=0):
        spend(depth);node=value['node']
        if isinstance(node,dict)and 'Bound'in node:
            index=node['Bound']
            return dict(sort=value['sort'],node={'Bound':index+amount if index>=local else index})
        nested=local+int(isinstance(node,dict)and 'Lambda'in node)
        return map_children(value,lambda child:shift(child,amount,nested,depth+1))
    def substitute(value,argument,local=0,depth=0):
        spend(depth);node=value['node']
        if isinstance(node,dict)and 'Bound'in node:
            index=node['Bound']
            if index==local:return shift(argument,local,depth=depth+1)
            return dict(sort=value['sort'],node={'Bound':index-1 if index>local else index})
        nested=local+int(isinstance(node,dict)and 'Lambda'in node)
        return map_children(value,lambda child:substitute(child,argument,nested,depth+1))
    current=term
    while True:
        node=current['node']
        if not isinstance(node,dict)or node.get('Op',[None])[0]!='apply':return current
        args=node['Op'][1]
        if len(args)!=2 or not isinstance(args[0]['node'],dict)or 'Lambda'not in args[0]['node']:return current
        spend(0)
        current=substitute(args[0]['node']['Lambda'],args[1])
