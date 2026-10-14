"""Untrusted proof-tree construction; all certificates still require replay."""

def nesting(value):
    if isinstance(value,dict):return 1+max((nesting(x) for x in value.values()),default=0)
    if isinstance(value,list):return 1+max((nesting(x) for x in value),default=0)
    return 0

def balance_transitivity(proof):
    """Reassociate only adjacent transitivity steps, retaining leaf order.

    Scopes such as induction, case branches, substitution and symmetry remain
    boundaries. Endpoints, terms, hypotheses and theorem references are unchanged.
    The checker must still derive each intermediate endpoint independently.
    """
    work=[0]
    def visit(value,depth=0):
        work[0]+=1
        if work[0]>1_000_000 or depth>256:raise ValueError('proof composition work limit')
        if isinstance(value,list):return [visit(x,depth+1) for x in value]
        if not isinstance(value,dict):return value
        if set(value)=={'Trans'}:
            pending=[value];leaves=[]
            while pending:
                step=pending.pop()
                if isinstance(step,dict) and set(step)=={'Trans'}:
                    pair=step['Trans']
                    if not isinstance(pair,list) or len(pair)!=2:raise ValueError('binary transitivity expected')
                    pending.extend(reversed(pair))
                    work[0]+=1
                    if work[0]>1_000_000:raise ValueError('proof composition work limit')
                else:leaves.append(visit(step,depth+1))
            def tree(start,end):
                if end-start==1:return leaves[start]
                middle=(start+end)//2
                return {'Trans':[tree(start,middle),tree(middle,end)]}
            return tree(0,len(leaves))
        return {k:visit(v,depth+1) for k,v in value.items()}
    return visit(proof)
