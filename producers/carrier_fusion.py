"""Universal map composition and ordered map/fold over arbitrary source carriers.

Recognition is untrusted producer work. Each proposal is an ordinary induction
law; literal lowering sees the checked single traversal in the selected source.
"""
from producers.semantic_laws import value,var,op,lam,bound,law

def specialize(subject,core=None):
    from ink_planner.semantic_search import positions,children,shift,map_children
    def operation(t):
        n=t['node'];return n.get('Op')if isinstance(n,dict)else None
    def closed(t,d=0):
        n=t['node'];return not(isinstance(n,dict)and 'Bound'in n and n['Bound']>=d)and all(closed(c,d+int('Lambda'in n))for c in children(t))
    def free(t,p):
        n=t['node']
        if isinstance(n,dict)and 'Free'in n:p[n['Free']]=t['sort']
        for c in children(t):free(c,p)
    def beta(t,argument,depth=0):
        n=t['node']
        if isinstance(n,dict)and 'Bound'in n:
            i=n['Bound']
            if i==depth:return shift(argument,depth)
            if i>depth:return bound(t['sort'],i-1)
        return map_children(t,lambda c:beta(c,argument,depth+int('Lambda'in n)))
    def simplify(t,budget):
        budget[0]-=1
        if budget[0]<0:raise ValueError('fusion simplification limit')
        t=map_children(t,lambda c:simplify(c,budget));o=operation(t)
        if o and o[0]=='apply'and 'Lambda'in o[1][0]['node']:
            return simplify(beta(o[1][0]['node']['Lambda'],o[1][1]),budget)
        return t
    rows=[]
    for name,root in sorted(subject['functions'].items()):
        for path,source in positions(root):
            outer=operation(source)
            if not outer or outer[0]not in ['method:map','call:foldr']or not closed(source):continue
            inner=operation(outer[1][0])
            if not inner or inner[0]!='method:map':continue
            xs,f=inner[1];a=value(xs['sort']['Value']['List']);b=value(outer[1][0]['sort']['Value']['List']);params={};free(source,params)
            sequence='fusion_sequence'
            while sequence in params:sequence+='_' 
            s=var(xs['sort'],sequence);mapped=op(outer[1][0]['sort'],'method:map',s,f)
            if outer[0]=='method:map':
                g=outer[1][1];c=value(source['sort']['Value']['List'])
                composed=lam(a,op(c,'apply',shift(g,1),op(b,'apply',shift(f,1),bound(a,0))))
                left=op(source['sort'],'method:map',mapped,g);right=op(source['sort'],'method:map',s,composed)
            else:
                initial,g=outer[1][1:];c=source['sort']
                composed=lam(a,lam(c,op(c,'apply',op(g['sort']['Arrow'][1],'apply',shift(g,2),op(b,'apply',shift(f,2),bound(a,1))),bound(c,0))))
                left=op(c,'call:foldr',mapped,initial,g);right=op(c,'call:foldr',s,initial,composed)
            params={};free(left,params)
            head='fusion_head';tail='fusion_tail'
            while head in params:head+='_' 
            while tail in params or head==tail:tail+='_' 
            proof={'Induction':dict(variable=sequence,names=[head,tail],base='Normalize',step='Normalize')}
            rows.append((name+'_carrier_fusion_'+'_'.join(map(str,path)),law(params,left,simplify(right,[8192]),proof)))
            if len(rows)>=256:return rows
    return rows
