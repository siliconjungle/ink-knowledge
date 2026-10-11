"""Move selection before construction using ordinary universal list proofs.

The untrusted simplifier only unfolds literal lambdas and record projections.
Every resulting proposal must pass the independent equality checker.
"""
from producers.semantic_laws import value, var, op, lam, bound, law


def specialize(subject, core):
    from ink_planner.semantic_search import positions, children, map_children, shift
    def beta(t, argument, depth=0):
        n=t['node']
        if isinstance(n,dict) and 'Bound' in n:
            i=n['Bound']
            if i==depth:return shift(argument,depth)
            if i>depth:return bound(t['sort'],i-1)
        return map_children(t,lambda c:beta(c,argument,depth+int(isinstance(n,dict) and 'Lambda' in n)))
    def simplify(t, budget):
        budget[0]-=1
        if budget[0]<0:raise ValueError('construction simplification limit')
        t=map_children(t,lambda c:simplify(c,budget))
        n=t['node'];operation=n.get('Op') if isinstance(n,dict) else None
        if not operation:return t
        name,args=operation
        if name=='apply' and isinstance(args[0]['node'],dict) and 'Lambda' in args[0]['node']:
            return simplify(beta(args[0]['node']['Lambda'],args[1]),budget)
        if name.startswith('field:'):
            constructor=args[0]['node'].get('Op') if isinstance(args[0]['node'],dict) else None
            if constructor and constructor[0].startswith('record:'):
                fields=core['program']['records'][constructor[0][7:]]
                index=next(i for i,(field,_) in enumerate(fields) if field==name[6:])
                return constructor[1][index]
        return t
    def closed(t, depth=0):
        n=t['node']
        return not(isinstance(n,dict) and 'Bound' in n and n['Bound']>=depth) and all(closed(c,depth+int(isinstance(n,dict) and 'Lambda' in n)) for c in children(t))
    rows=[]
    for name,root in sorted(subject['functions'].items()):
        for path,source in positions(root):
            n=source['node'];outer=n.get('Op') if isinstance(n,dict) else None
            if not outer or outer[0]!='method:filter' or not closed(source):continue
            mapped,p=outer[1]
            inner=mapped['node'].get('Op') if isinstance(mapped['node'],dict) else None
            if not inner or inner[0]!='method:map':continue
            xs,f=inner[1];A=value(xs['sort']['Value']['List']);B=value(mapped['sort']['Value']['List'])
            predicate=lam(A,op(value('Bool'),'apply',shift(p,1),op(B,'apply',shift(f,1),bound(A,0))))
            predicate=simplify(predicate,[8192])
            target=op(source['sort'],'method:map',op(xs['sort'],'method:filter',xs,predicate),f)
            variable='collect_sequence'
            def free(t,params):
                n=t['node']
                if isinstance(n,dict) and 'Free' in n:params[n['Free']]=t['sort']
                for c in children(t):free(c,params)
            params={};free(source,params)
            while variable in params:variable+='_' 
            sequence=var(xs['sort'],variable)
            # Captures in f/p remain independent parameters of the theorem.
            # Generalise the iteration receiver, not equal-looking captured terms.
            left=op(source['sort'],'method:filter',op(mapped['sort'],'method:map',sequence,f),p)
            right=op(source['sort'],'method:map',op(xs['sort'],'method:filter',sequence,predicate),f)
            params={};free(left,params)
            head='collect_head'
            while head in params:head+='_' 
            tail='collect_tail'
            while tail in params or tail==head:tail+='_' 
            condition=op(value('Bool'),'apply',p,op(B,'apply',f,var(A,head)))
            proof={'Induction':dict(variable=variable,names=[head,tail],base='Normalize',step={'Cases':dict(condition=condition,on_false='Normalize',on_true='Normalize')})}
            rows.append((name+'_select_before_build_'+'_'.join(map(str,path)),law(params,left,right,proof)))
            if len(rows)>=256:return rows
    return rows
