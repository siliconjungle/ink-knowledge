"""Collapse per-element list construction into ordinary bulk map/concat.

The source is a pure right fold; its element order and arbitrary suffix are
unchanged. No effectful action or intermediate observation is discarded.
"""
from producers.semantic_laws import value, arrow, var, bound, term, op, lam, law, word

CARRIERS=('U32','U64','I32','F32','Bool','String','Int','Unit')


def make(a,b,append=False):
    A,B=value(a),value(b);XS,YS=value({'List':a}),value({'List':b})
    xs,ys=var(XS,'bulk_xs'),var(YS,'bulk_suffix');F=arrow(A,B);f=var(F,'bulk_f')
    item=op(B,'apply',f,bound(A,1));singleton=op(YS,'method:freeze',op(value({'Buffer':b}),'call:buffer_fill',word('U32',1),item))
    step=lam(A,lam(YS,op(YS,'method:concat',bound(YS,0),singleton) if append else op(YS,'method:concat',singleton,bound(YS,0))))
    source=op(YS,'call:foldr',xs,ys,step)
    if append:
        BS=value({'Buffer':b})
        owned=lam(A,lam(BS,op(BS,'method:push',bound(BS,0),item)))
        target=op(YS,'method:freeze',op(BS,'call:foldr',xs,op(BS,'call:buffer',ys),owned))
    else:target=op(YS,'method:concat',op(YS,'method:map',xs,f),ys)
    proof={'Induction':dict(variable='bulk_xs',names=['bulk_head','bulk_tail'],base='Normalize',step='Normalize')}
    return law(dict(bulk_xs=XS,bulk_suffix=YS,bulk_f=F),source,target,proof)


def named_laws():return [(f'bulk/fold-{"owned-append" if append else "map"}-{a.lower()}-{b.lower()}',make(a,b,append)) for append in [False,True] for a in CARRIERS for b in CARRIERS]


def specialize(subject,core=None):
    from ink_planner.semantic_search import positions,children,shift
    rows=[]
    for name,root in sorted(subject['functions'].items()):
        for path,source in positions(root):
            node=source['node'];operator=node.get('Op') if isinstance(node,dict) else None
            if not operator or operator[0]!='call:foldr':continue
            xs,initial,step=operator[1]
            if not isinstance(step['node'],dict) or 'Lambda' not in step['node']:continue
            inner=step['node']['Lambda']
            if not isinstance(inner['node'],dict) or 'Lambda' not in inner['node']:continue
            body=inner['node']['Lambda'];operation=body['node'].get('Op') if isinstance(body['node'],dict) else None
            if not operation or operation[0]!='method:concat':continue
            singleton,acc=operation[1];append=singleton['node']=={'Bound':0}
            if append:acc,singleton=operation[1]
            if acc['node']!={'Bound':0} or not isinstance(singleton['node'],dict):continue
            if 'Cons' in singleton['node']:
                item,nil=singleton['node']['Cons']
                if nil['node']!='Nil':continue
            else:
                freezing=singleton['node'].get('Op')
                if not freezing or freezing[0]!='method:freeze':continue
                filling=freezing[1][0]['node'].get('Op')
                if not filling or filling[0]!='call:buffer_fill' or filling[1][0]!=word('U32',1):continue
                item=filling[1][1]
            def mentions_acc(t,depth=0):
                n=t['node']
                return isinstance(n,dict) and n.get('Bound')==depth or any(mentions_acc(c,depth+int(isinstance(n,dict) and 'Lambda' in n)) for c in children(t))
            if mentions_acc(item):continue
            # Removing only the accumulator binder leaves the element binder.
            if append:
                BS=value({'Buffer':source['sort']['Value']['List']})
                owned=lam(step['sort']['Arrow'][0],lam(BS,op(BS,'method:push',bound(BS,0),item)))
                target=op(source['sort'],'method:freeze',op(BS,'call:foldr',xs,op(BS,'call:buffer',initial),owned))
            else:
                mapper=lam(step['sort']['Arrow'][0],shift(item,-1))
                target=op(source['sort'],'method:concat',op(source['sort'],'method:map',xs,mapper),initial)
            params={}
            def free(t):
                n=t['node']
                if isinstance(n,dict) and 'Free' in n:params[n['Free']]=t['sort']
                for c in children(t):free(c)
            free(source)
            # Open surrounding lambdas are not standalone proof environments.
            def closed(t,depth=0):
                n=t['node']
                return not(isinstance(n,dict) and 'Bound' in n and n['Bound']>=depth) and all(closed(c,depth+int(isinstance(n,dict) and 'Lambda' in n)) for c in children(t))
            if not closed(source):continue
            variable='bulk_sequence'
            while variable in params:variable+='_'
            head,tail='bulk_head','bulk_tail'
            while head in params or head==variable:head+='_'
            while tail in params or tail in (variable,head):tail+='_'
            params[variable]=xs['sort']
            from ink_planner.semantic_search import map_children
            def abstract(t):return var(xs['sort'],variable) if t==xs else map_children(t,abstract)
            source_generic=abstract(source)
            target_generic=abstract(target)
            params={};free(source_generic)
            proof={'Induction':dict(variable=variable,names=[head,tail],base='Normalize',step='Normalize')}
            rows.append((name+'_bulk_'+'_'.join(map(str,path)),law(params,source_generic,target_generic,proof)))
            if len(rows)>=256:return rows
    return rows
