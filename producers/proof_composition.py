"""Untrusted proof-tree construction; all certificates still require replay."""

def fresh_bindings(stems, occupied=()):
    """Choose distinct proposal names without shadowing an ambient scope."""
    occupied=set(occupied);names=[]
    for stem in stems:
        name=stem;serial=0
        while name in occupied:
            serial+=1;name=stem+'_'+str(serial)
        occupied.add(name);names.append(name)
    return names

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


def freshen_match_terms(proof,parameters=()):
    """Avoid lexical shadowing when closed terms are composed under proof scopes.

    Only Match-bound names and their lexical references change. The source
    statement, free variables, theorem references and hypotheses stay fixed.
    The kernel still checks alpha-equivalence and the entire resulting proof.
    """
    from producers.equational import fresh_alpha
    work=[0]
    def visit(value,env,depth=0):
        work[0]+=1
        if work[0]>1_000_000 or depth>256:raise ValueError('proof hygiene resource limit')
        if isinstance(value,list):return [visit(x,env,depth+1)for x in value]
        if not isinstance(value,dict):return value
        if set(value)=={'Match'}:return fresh_alpha(value,{n:n for n in env})
        if set(value)=={'Substitute'}:
            x=value['Substitute']
            return {'Substitute':{**x,'context':visit(x['context'],env|{x['variable']},depth+1),'equality':visit(x['equality'],env,depth+1)}}
        for kind in ['Cases','Induction','GeneralizedInduction']:
            if set(value)=={kind}:
                x=value[kind];out={k:visit(v,env,depth+1)for k,v in x.items()if k!='cases'}
                out['cases']=[{**case,'proof':visit(case['proof'],env|set(case['bindings']),depth+1)}for case in x['cases']]
                return {kind:out}
        return {k:visit(v,env,depth+1)for k,v in value.items()}
    return visit(proof,set(parameters))
