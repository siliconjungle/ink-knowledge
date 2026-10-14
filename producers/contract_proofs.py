"""Untrusted source-contract proof authoring and canonical database publication.

Every proposed proof is replayed against the compiler's source-derived obligation.
The catalogue records correctness; measurements separately establish profitability.
"""
import argparse, json, subprocess
from pathlib import Path
from ink_knowledge.store import Store, entry, semantic_entry, identity
from producers.equational import Tactic, convert
from producers.action_replacement import var, cons
from producers.point_delta import sub, normal
from producers.beta_specialization15 import beta_normalize

MATH='first-order-inductive-equality-v1'

def pure_proposals(goal):
    """Ordinary proof terms, independent of proposition/algorithm names.

    Enumerate conversion, scoped hypotheses, Boolean splitting and induction.
    The compiler replays every proposal. Bounded failure grants no assumption.
    """
    yield 'Normalize'
    for i in range(len(goal['conditions'])):yield {'Hypothesis':i}
    yield {'Linear':dict(premises=[])}
    for i in range(len(goal['conditions'])):yield {'Linear':dict(premises=[[i,1]])}
    if len(goal['conditions'])>1:yield {'Linear':dict(premises=[[i,1]for i in range(len(goal['conditions']))])}
    from ink_planner.semantic_search import children
    conditions=[];seen=set();guards=[];guard_seen=set()
    def closed(term,binders=0):
        node=term.get('node')
        if isinstance(node,dict) and 'Bound' in node:return node['Bound']<binders
        nested=binders+int(isinstance(node,dict) and 'Lambda' in node)
        return all(closed(child,nested) for child in children(term))
    def visit(term,depth=0):
        if depth>64:return
        node=term.get('node')
        if isinstance(node,dict)and 'Lambda'in node:return
        if term.get('sort')=={'Value':'Bool'}:
            data=json.dumps(term,sort_keys=True)
            if closed(term) and data not in seen:
                seen.add(data);conditions.append(term)
        if isinstance(node,dict) and node.get('Op',[None])[0]=='call:choose':
            guard=node['Op'][1][0]
            # Splitting p also decides p == false/true, and leaves the useful
            # positive predicate available to result-validity normalization.
            comparison=guard['node'].get('Op') if isinstance(guard['node'],dict) else None
            if comparison and comparison[0] in ('binary:==','binary:!='):
                left,right=comparison[1]
                if left['sort']=={'Value':'Bool'} and isinstance(right['node'],dict) and 'Bool'in right['node']:guard=left
                elif right['sort']=={'Value':'Bool'} and isinstance(left['node'],dict) and 'Bool'in left['node']:guard=right
            data=json.dumps(guard,sort_keys=True)
            if closed(guard) and data not in guard_seen:
                guard_seen.add(data);guards.append(guard)
        for child in children(term):visit(child,depth+1)
    for term in [goal['goal']['from'],goal['goal']['to']]:
        # Surface let/loop elaboration can leave branch guards behind known
        # callback applications. Normalize their binders before proposing cases;
        # the kernel still checks each original closed obligation.
        try:visit(beta_normalize(term,budget=100000))
        except ValueError:pass
        visit(term)
    for name,sort in goal['params'].items():
        if sort=={'Value':'Bool'}:
            term=dict(sort=sort,node={'Free':name})
            if term not in conditions:conditions.append(term)
    # Branch guards select the result before its observer runs. Prioritize them
    # over the entire Boolean goal, including closed guards with local callbacks.
    # This is bounded untrusted search; each leaf still proves the original goal.
    guards=[c for c in guards if not isinstance(c['node'],dict) or 'Bool'not in c['node']][:4]
    if guards:
        proof='Normalize'
        for guard in reversed(guards):proof={'Cases':dict(condition=guard,on_false=proof,on_true=proof)}
        yield proof
    conditions=[c for c in conditions if not isinstance(c['node'],dict)or 'Bool'not in c['node']][:12]
    for condition in conditions:
        yield {'Cases':dict(condition=condition,on_false='Normalize',on_true='Normalize')}
    # Compose a bounded set of cases rather than recognise a particular formula.
    if 1<len(conditions)<=4:
        proof='Normalize'
        for condition in reversed(conditions):proof={'Cases':dict(condition=condition,on_false=proof,on_true=proof)}
        yield proof
    for name,sort in goal['params'].items():
        value=sort.get('Value') if isinstance(sort,dict) else None
        if isinstance(value,dict) and any(k in value for k in ('Option','Result')):
            names=[]
            for i in range(2 if 'Result' in value else 1):
                payload=f'contract_payload_{i}'
                while payload in goal['params'] or payload in names:payload+='_'
                names.append(payload)
            yield {'Variants':dict(variable=name,names=names,first='Normalize',second='Normalize')}
        if isinstance(sort,dict)and isinstance(sort.get('Value'),dict)and 'List'in sort['Value']:
            head,tail='contract_head','contract_tail'
            while head in goal['params']:head+='_' 
            while tail in goal['params']:tail+='_' 
            yield {'Induction':dict(variable=name,names=[head,tail],base='Normalize',step='Normalize')}

def proof_semantics(proof):
    """Mirror the kernel's marker requirement; the marker grants no authority."""
    def general(p):
        if not isinstance(p,dict):return False
        if 'Variants' in p or 'Assume' in p:return True
        if 'Use' in p:
            use=p['Use']
            return bool(use.get('types') or use.get('assumptions')) or any(general(x) for x in use.get('premises',[]))
        if 'AssertEquality' in p:return general(p['AssertEquality']['premise']) or general(p['AssertEquality']['body'])
        if 'Sym' in p:return general(p['Sym'])
        if 'Trans' in p:return general(p['Trans']['left']) or general(p['Trans']['right'])
        if 'Congruence' in p:return any(general(x) for x in p['Congruence'])
        if 'Forall' in p:return general(p['Forall']['body'])
        if 'Cases' in p:return general(p['Cases']['on_false']) or general(p['Cases']['on_true'])
        for kind in ('Induction','GeneralizedInduction'):
            if kind in p:return general(p[kind]['base']) or general(p[kind]['step'])
        return False
    return 'ink-general-laws-v1' if general(proof) else 'ink-conditional-laws-v1'

def rewrite_proposals(goal,store,limit=64):
    """Compose ordinary database laws through the exact obligation context.

    This bounded search has no privileged collection/property names. Lambda
    interiors are left to binder-aware producers; closed argument positions
    support arbitrary surrounding observations, including multiset contracts.
    """
    from ink_planner.semantic_search import children,match,substitute,replace,key
    from producers.beta_specialization15 import lift_use
    def positions(term,path=()):
        yield path,term
        if isinstance(term['node'],dict)and 'Lambda'in term['node']:return
        for i,child in enumerate(children(term)):yield from positions(child,path+(i,))
    def size(term):return 1+sum(size(child)for child in children(term))
    frontier=[(goal['goal']['from'],None,())];seen={key(goal['goal']['from'])};attempts=0
    cache={}
    for _ in range(8):
        next_frontier=[]
        for body,prior,dependencies in frontier:
            for path,target in positions(body):
                node=target['node']
                if not isinstance(node,dict)or 'Op'not in node:continue
                operation=node['Op'][0];query_key=(key(target['sort']),operation)
                if query_key not in cache:
                    rows=[];after=None
                    while len(rows)<1024:
                        page=store.query(kind='rewrite',semantics='ink-conditional-laws-v1',result=target['sort'],operation=operation,after=after,limit=128)
                        for ident in page:
                            payload=store.object(ident)['payload']
                            head=payload['from'].get('node',{})
                            if isinstance(head,dict)and head.get('Op',[None])[0]==operation:rows.append((ident,payload))
                        if len(page)<128:break
                        after=page[-1]
                    cache[query_key]=rows
                for ident,law in cache[query_key]:
                        args={}
                        if law.get('types')or law.get('assumptions'):continue
                        if not match(law['from'],target,law['params'],args)or set(args)!=set(law['params']):continue
                        replacement=substitute(law['to'],args)
                        if size(replacement)>=size(target):continue
                        updated=replace(body,path,replacement);fingerprint=key(updated)
                        if fingerprint in seen:continue
                        seen.add(fingerprint)
                        roots=tuple(sorted(set(dependencies)|{ident}));bundle=store.bundle(roots)
                        use={'Use':dict(law=ident,arguments=args,premises=['Normalize']*len(law['conditions']))}
                        step=lift_use(body,path,use)
                        chain=step if prior is None else {'Trans':dict(middle=body,left=prior,right=step)}
                        reduced={**goal,'goal':dict(**{'from':updated,'to':goal['goal']['to']})}
                        # Replay even small proof proposals before retaining a path.
                        for terminal in pure_proposals(reduced):
                            if attempts>=limit:return
                            attempts+=1
                            yield {'Trans':dict(middle=updated,left=chain,right=terminal)},bundle
                        next_frontier.append((updated,chain,roots))
                        if len(next_frontier)>=8:break
                if len(next_frontier)>=8:break
            if len(next_frontier)>=8:break
        frontier=next_frontier
        if not frontier:return

def references(value):
    if isinstance(value,list):return set().union(*(references(x) for x in value))
    if not isinstance(value,dict):return set()
    found={v for k,v in value.items() if k in ('Data','datatype','function','theorem') and isinstance(v,str) and len(v)==64}
    return found|set().union(*(references(x) for x in value.values()))

def context_for(context,goal):
    """Keep only definitions and value types actually mentioned by this law."""
    functions=set();types=set()
    def scan(t):
        if isinstance(t,dict):
            op=t.get('Op')
            if isinstance(op,list) and op and isinstance(op[0],str) and op[0].startswith('call:') and op[0][5:] in context['definitions']:functions.add(op[0][5:])
            if isinstance(t.get('Named'),str):types.add(t['Named'])
            for v in t.values():scan(v)
        elif isinstance(t,list):
            for v in t:scan(v)
    scan(goal);seen=set()
    while functions-seen:
        name=next(iter(functions-seen));seen.add(name);definition=context['definitions'][name]
        scan(definition);functions.update(definition['definition']['callees'])
    seen_types=set()
    while types-seen_types:
        name=next(iter(types-seen_types));seen_types.add(name);scan(context['records'].get(name,[]))
    groups={i:members for i,members in context.get('recursive_groups',{}).items() if any(n in functions for n in members)}
    if any(not set(members)<=functions for members in groups.values()):raise ValueError('recursive context closure incomplete')
    return dict(schema=1,definitions={n:context['definitions'][n] for n in sorted(functions)},records={n:t for n,t in context['records'].items() if n in types},enums={n:t for n,t in context['enums'].items() if n in types},**({'ids':[n for n in context.get('ids',[]) if n in types]} if any(n in types for n in context.get('ids',[])) else {}),**({'recursive_groups':groups} if groups else {}))

def state_proof(objects,a,z,params,hyp=(),depth=0,serial=None,aliases=None,scalar=None,lemma_attempts=None,strengthen=True):
    proof=_state_proof(objects,a,z,params,hyp,depth,serial,aliases,scalar,lemma_attempts,strengthen)
    if scalar is None:return proof
    from producers.point_delta import free_variables
    from producers.proof_composition import nesting
    # Close a deep branch under its exact typed parameters and premises. A use
    # proves every original premise again; induction/case hypotheses retain their
    # local indices. No branch fact becomes an unconditional global theorem.
    if nesting(proof)<=24 or [i for _,_,i in hyp]!=list(range(len(hyp))):return proof
    free=free_variables(a)|free_variables(z)|set().union(*(free_variables(x)|free_variables(y) for x,y,_ in hyp))
    if not free<=params.keys():return proof
    theorem=scalar.add({'Theorem':dict(params=list(params.items()),
        conditions=[dict(**{'from':x,'to':y}) for x,y,_ in hyp],
        **{'from':a,'to':z},proof=proof)})
    return {'Use':dict(theorem=theorem,arguments=[var(n) for n in params],
        premises=[{'Hypothesis':i} for _,_,i in hyp])}

def _state_proof(objects,a,z,params,hyp=(),depth=0,serial=None,aliases=None,scalar=None,lemma_attempts=None,strengthen=True):
    """Bounded ordinary constructor induction and Boolean case proof search."""
    if depth>18:raise ValueError('contract proof search depth')
    serial=serial if serial is not None else [0,0]
    lemma_attempts=lemma_attempts if lemma_attempts is not None else set()
    serial[1]+=1
    if serial[1]>100000:raise ValueError("contract proof search node budget")
    class ContractTactic(Tactic):
        def norm(self, value):
            def reflexive(t):
                if isinstance(t,list):return [reflexive(x) for x in t]
                if not isinstance(t,dict):return t
                t={k:reflexive(v) for k,v in t.items()}
                if 'Binary' in t:
                    b=t['Binary']
                    if b['op']=='==' and b['left']==b['right']:return {'Bool':True}
                return t
            value=super().norm(value)
            for _ in range(32):
                updated=reflexive(value)
                if updated==value:return value
                value=super().norm(updated)
            raise ValueError('contract normalization budget')
    tactic=ContractTactic(objects)
    from producers.action_replacement import trans
    from producers.point_delta import lift
    from producers.equational import alpha
    def replace(t,old,new):
        if alpha(t)==alpha(old):return new
        if isinstance(t,dict):return {k:replace(v,old,new) for k,v in t.items()}
        if isinstance(t,list):return [replace(v,old,new) for v in t]
        return t
    from producers.point_delta import free_variables
    aliases=aliases or {}
    def canonical(value):
        current=tactic.norm(value);proof=convert(value,current)
        def find(t):
            if isinstance(t,dict):
                if 'Call' in t and t['Call']['function'] in aliases and free_variables(t)<=params.keys():
                    target,_=aliases[t['Call']['function']];args=t['Call']['arguments']
                    if target is not None or (len(args)==2 and alpha(args[0])==alpha(args[1])):return t
                for x in t.values():
                    found=find(x)
                    if found:return found
            elif isinstance(t,list):
                for x in t:
                    found=find(x)
                    if found:return found
        for _ in range(256):
            found=find(current)
            if found is None:return current,proof
            target,theorem=aliases[found['Call']['function']]
            replacement={'Call':dict(function=target,arguments=found['Call']['arguments'])} if target is not None else {'Bool':True}
            following=replace(current,found,replacement)
            use={'Use':dict(theorem=theorem,arguments=found['Call']['arguments'] if target is not None else found['Call']['arguments'][:1],premises=[])}
            proof=trans(proof,lift(use,replace(current,found,var('delta_hole'))),convert(following,tactic.norm(following)))
            current=tactic.norm(following)
        raise ValueError('contract alias rewrite budget')
    facts=[]
    for x,y,i in hyp:
        xx,px=canonical(x);yy,py=canonical(y)
        facts.append((xx,yy,trans({'Sym':px},{'Hypothesis':i},py)))
    from producers.conditional_induction import boolean_library
    boolean_objects,boolean_ids=boolean_library();objects.update(boolean_objects)
    def expand_boolean_facts():
        index=0
        while index<len(facts):
            if len(facts)>256:raise ValueError('contract Boolean fact budget')
            x,y,proof=facts[index];index+=1
            branch=x.get('If') if isinstance(x,dict) else None
            if y!={'Bool':True} or branch is None or branch['on_false']!={'Bool':False}:continue
            for label,value in [('left',branch['condition']),('right',branch['on_true'])]:
                if value=={'Bool':True} or any(alpha(value)==alpha(a) and b=={'Bool':True} for a,b,_ in facts):continue
                use={'Use':dict(theorem=boolean_ids[label],arguments=[branch['condition'],branch['on_true']],premises=[proof])}
                facts.append((value,{'Bool':True},use))
    expand_boolean_facts()
    def expand_constructor_facts():
        # Elimination of a matched result can hide the state expression that
        # produced its payload. Recover field equalities by ordinary congruence
        # through a total Match projection; constructor identity is checked data.
        def bindings(i,constructor):
            result=[]
            for j in range(len(constructor['fields'])):
                name=f'contract_project_{i}_{j}'
                while name in params or name in result:name+='_'
                result.append(name)
            return result
        for x,y,proof in list(facts):
            if 'Construct' not in x or 'Construct' not in y:continue
            a=x['Construct'];b=y['Construct']
            if a['datatype']!=b['datatype']:continue
            constructors=objects[a['datatype']]['payload']['declaration']['Datatype']['constructors']
            if a['constructor']!=b['constructor']:
                branches=[dict(bindings=bindings(i,c),body={'Bool':i==a['constructor']}) for i,c in enumerate(constructors)]
                projected=lift(proof,{'Match':dict(scrutinee=var('delta_hole'),branches=branches)})
                facts.append(({'Bool':True},{'Bool':False},projected));continue
            for field,(left,right) in enumerate(zip(a['arguments'],b['arguments'])):
                if left==right:continue
                branches=[]
                for i,c in enumerate(constructors):
                    names=bindings(i,c)
                    branches.append(dict(bindings=names,body=var(names[field]) if i==a['constructor'] else left))
                projected=lift(proof,{'Match':dict(scrutinee=var('delta_hole'),branches=branches)})
                if 'Var' in right and 'Var' not in left:left,right,projected=right,left,{'Sym':projected}
                if not any(alpha(left)==alpha(a) and alpha(right)==alpha(b) for a,b,_ in facts):
                    facts.append((left,right,projected))
    expand_constructor_facts()
    def contradiction():
        for x,y,proof in facts:
            if 'Bool' in x and 'Bool' in y and x!=y:
                context={'If':dict(condition=var('delta_hole'),on_true=a if x['Bool'] else z,on_false=z if x['Bool'] else a)}
                return trans(convert(a,sub(context,{'delta_hole':x})),lift(proof,context),convert(sub(context,{'delta_hole':y}),z))
        return None
    impossible=contradiction()
    if impossible:return impossible
    def simplify(value,others):
        current,proof=canonical(value)
        for _ in range(16):
            changed=False
            for x,y,p in others:
                if x==y:continue
                following=replace(current,x,y)
                if following!=current:
                    updated,computed=canonical(following)
                    proof=trans(proof,lift(p,replace(current,x,var('delta_hole'))),computed)
                    current=updated;changed=True;break
            if not changed:return current,proof
        raise ValueError('contract fact rewrite budget')
    for _ in range(4):
        updated=False
        for i,(x,y,p) in enumerate(facts):
            others=facts[:i]+facts[i+1:];xx,px=simplify(x,others);yy,py=simplify(y,others)
            if (xx,yy)!=(x,y):facts[i]=(xx,yy,trans({'Sym':px},p,py));updated=True
            impossible=contradiction()
            if impossible:return impossible
        if not updated:break
        expand_boolean_facts()
        expand_constructor_facts()
    na,pa=simplify(a,facts);nz,pz=simplify(z,facts)
    def nodes(t):
        if isinstance(t,dict):
            yield t
            if 'Match' in t:yield from nodes(t['Match']['scrutinee']);return
            for x in t.values():yield from nodes(x)
        elif isinstance(t,list):
            for x in t:yield from nodes(x)
    if na==nz or ('Binary' in na and na['Binary']['op']=='==' and na['Binary']['left']==na['Binary']['right'] and nz=={'Bool':True}):
        return trans(pa,convert(na,nz),{'Sym':pz})
    if scalar is not None:
        try:return trans(pa,scalar.prove(na,nz,params,facts),{'Sym':pz})
        except ValueError:pass
    # A recursive observation can have a concrete result after preceding writes,
    # even when embedded in a traversal over an independent collection. Propose
    # a closed equality first, replay it as a separate ordinary theorem, then
    # transport that fact by congruence. Literal/constructor candidates are search
    # data; their names or shape never grant admission.
    if strengthen and scalar is not None and len(lemma_attempts)<16:
        literals=[]
        pending=[na,nz]
        while pending:
            term=pending.pop()
            if isinstance(term,dict):
                if set(term)=={'U64'} and term not in literals:literals.append(term)
                pending.extend(term.values())
            elif isinstance(term,list):pending.extend(term)
        literals=literals[:8]
        for term in nodes([na,nz]):
            if 'Call' not in term or not free_variables(term)<=params.keys():continue
            declaration=objects[term['Call']['function']]['payload']['declaration'].get('Function')
            sort=declaration and declaration['result']
            if not isinstance(sort,dict) or 'Data' not in sort:continue
            constructors=objects[sort['Data']]['payload']['declaration'].get('Datatype',{}).get('constructors',[])
            for ordinal,constructor in enumerate(constructors):
                fields=constructor['fields']
                if len(fields)>1 or any(t not in ('Bool','U64') for t in fields):continue
                candidates=[[]] if not fields else ([[v] for v in literals] if fields[0]=='U64' else [[{'Bool':False}],[{'Bool':True}]])
                for arguments in candidates:
                    if len(lemma_attempts)>=16:break
                    value=cons(sort['Data'],ordinal,arguments)
                    marker=json.dumps(['observation',term,value],sort_keys=True,separators=(',',':'))
                    if marker in lemma_attempts:continue
                    lemma_attempts.add(marker)
                    local={n:t for n,t in params.items() if n in free_variables(term)}
                    try:proof=state_proof(objects,term,value,local,(),0,serial,aliases,scalar,lemma_attempts,False)
                    except ValueError:continue
                    theorem=scalar.add({'Theorem':dict(params=list(local.items()),conditions=[],**{'from':term,'to':value},proof=proof)})
                    use={'Use':dict(theorem=theorem,arguments=[var(n) for n in local],premises=[])}
                    following=replace(na,term,value)
                    proof=state_proof(objects,following,nz,params,hyp,depth+1,serial,aliases,scalar,lemma_attempts,strengthen)
                    return trans(pa,lift(use,replace(na,term,var('delta_hole'))),proof,{'Sym':pz})
    # A whole-action induction hypothesis can be too weak for a recursive helper
    # reached through a different branch. Propose a stronger, separately proved
    # conditional lemma about the residual computation itself. Dependent outer
    # premises never become tail assumptions: they are quantified inside the
    # new proposition, and only independent premises enter its proof context.
    if strengthen and scalar is not None and len(lemma_attempts)<16:
        target_variables=free_variables(na)|free_variables(nz)
        for variable,sort in params.items():
            if variable not in target_variables or not isinstance(sort,dict) or 'Data' not in sort:continue
            declaration=objects[sort['Data']]['payload']['declaration'].get('Datatype',{})
            if not any('SelfType' in constructor['fields'] for constructor in declaration.get('constructors',[])):continue
            if not any(variable in free_variables(x)|free_variables(y) for x,y,_ in hyp):continue
            independent=[(x,y,p) for x,y,p in facts if variable not in free_variables(x)|free_variables(y)
                and (free_variables(x)|free_variables(y))&target_variables and x!=y]
            for predicate,truth,predicate_proof in facts:
                if len(lemma_attempts)>=16:break
                if truth!={'Bool':True} or 'Call' not in predicate or variable not in free_variables(predicate):continue
                statement={'If':dict(condition=predicate,on_true=na,on_false=nz)}
                marker=json.dumps([statement,nz,[[x,y] for x,y,_ in independent]],sort_keys=True,separators=(',',':'))
                if marker in lemma_attempts:continue
                lemma_attempts.add(marker)
                premises=[(x,y,i) for i,(x,y,_) in enumerate(independent)]
                try:
                    proof=state_proof(objects,statement,nz,params,premises,0,serial,aliases,scalar,lemma_attempts,False)
                except ValueError:continue
                conditions=[dict(**{'from':x,'to':y}) for x,y,_ in independent]
                theorem=scalar.add({'Theorem':dict(params=list(params.items()),conditions=conditions,
                    **{'from':statement,'to':nz},proof=proof)})
                use={'Use':dict(theorem=theorem,arguments=[var(n) for n in params],premises=[p for _,_,p in independent])}
                context={'If':dict(condition=var('delta_hole'),on_true=na,on_false=nz)}
                return trans(pa,convert(na,sub(context,{'delta_hole':{'Bool':True}})),
                    {'Sym':lift(predicate_proof,context)},use,{'Sym':pz})
    from producers.point_delta import free_variables
    # An inconsistent branch can reduce the goal to false=true while retaining
    # a conditional selector in its premises. Split those selectors too; every
    # resulting branch is ordinary evidence, never an assumed contradiction.
    selectors={}
    for t in nodes([na,nz,*[value for x,y,_ in facts for value in (x,y)]]):
        if 'If' not in t:continue
        condition=t['If']['condition'];variables=free_variables(condition)
        if not variables<=params.keys():continue
        if any(n in variables and isinstance(sort,dict) and 'Data' in sort
            and all(n not in free_variables(x)|free_variables(y) for x,y,_ in hyp)
            for n,sort in params.items()):continue
        reduced,_=simplify(condition,facts)
        if 'Bool' in reduced:continue
        # Splitting an already established selector spends depth without learning
        # anything. Prefer small scalar selectors inside compound premises, so
        # an impossible outer condition is exposed by its actual branch choices.
        fingerprint=json.dumps(alpha(reduced),sort_keys=True,separators=(',',':'))
        selectors.setdefault(fingerprint,reduced)
    for fingerprint,condition in sorted(selectors.items(),key=lambda item:(len(item[0]),item[0])):
        cases={}
        for field,flag in [('on_false',False),('on_true',True)]:
            cases[field]=state_proof(objects,na,nz,params,[*hyp,(condition,{'Bool':flag},len(hyp))],depth+1,serial,aliases,scalar,lemma_attempts,strengthen)
        return trans(pa,{'BoolSplit':dict(condition=condition,**{'from':na,'to':nz},**cases)},{'Sym':pz})
    from producers.point_delta import free_variables
    # Eliminate an observed constructor shared with a premise without inventing
    # an induction hypothesis for that premise.
    def all_nodes(t):
        if isinstance(t,dict):
            yield t
            for x in t.values():yield from all_nodes(x)
        elif isinstance(t,list):
            for x in t:yield from all_nodes(x)
    premise_nodes=list(all_nodes([x for x,y,p in facts]))
    for node in nodes([na,nz]):
        if 'Match' not in node:continue
        scrutinee=node['Match']['scrutinee']
        if 'Call' not in scrutinee or not any(alpha(scrutinee)==alpha(x) for x in premise_nodes) or not free_variables(scrutinee)<=params.keys():continue
        sort=objects[scrutinee['Call']['function']]['payload']['declaration']['Function']['result']
        if not isinstance(sort,dict) or 'Data' not in sort:continue
        datatype=sort['Data'];cases=[]
        for i,c in enumerate(objects[datatype]['payload']['declaration']['Datatype']['constructors']):
            serial[0]+=1;names=[f'contract_observed_{serial[0]}_{j}' for j in range(len(c['fields']))]
            fields=[sort if t=='SelfType' else t for t in c['fields']];local={**params,**dict(zip(names,fields))}
            value=cons(datatype,i,[var(n) for n in names])
            proof=state_proof(objects,na,nz,local,[*hyp,(scrutinee,value,len(hyp))],depth+1,serial,aliases,scalar,lemma_attempts,strengthen)
            cases.append(dict(bindings=names,proof=proof))
        return trans(pa,{'Cases':dict(scrutinee=scrutinee,**{'from':na,'to':nz},cases=cases)},{'Sym':pz})
    free=free_variables(na)|free_variables(nz)
    # Relevant relational premises may contain the origin of a scalar payload
    # after the goal itself no longer mentions that origin. Case analysis must
    # retain this dependency rather than treating the payload as unconstrained.
    while True:
        before=len(free)
        for x,y,_ in facts:
            variables=free_variables(x)|free_variables(y)
            if variables&free:free.update(variables)
        if len(free)==before:break
    preferred=[]
    for node in nodes([na,nz]):
        if 'Match' in node and 'Var' in node['Match']['scrutinee']:
            preferred.append(node['Match']['scrutinee']['Var'])
        if 'Call' in node:
            call=node['Call'];definition=objects[call['function']]['payload']['declaration'].get('Function')
            if definition and definition['recursive'] is not None:
                argument=call['arguments'][definition['recursive']]
                if 'Var' in argument:preferred.append(argument['Var'])
    for variable in dict.fromkeys([*preferred,*params]):
        if variable not in params:continue
        sort=params[variable]
        if variable not in free or not isinstance(sort,dict) or 'Data' not in sort:continue
        datatype=sort['Data'];d=objects[datatype]['payload']['declaration']
        if 'Datatype' not in d:continue
        induct=all(variable not in free_variables(x)|free_variables(y) for x,y,_ in hyp)
        cases=[]
        for i,c in enumerate(d['Datatype']['constructors']):
            serial[0]+=1;names=[f'contract_case_{serial[0]}_{j}' for j in range(len(c['fields']))]
            value=cons(datatype,i,[var(n) for n in names]);binding={variable:value};local={n:t for n,t in params.items() if n!=variable}
            fields=[sort if t=='SelfType' else t for t in c['fields']];local.update(zip(names,fields))
            premises=list(hyp) if induct else [(sub(x,binding),sub(y,binding),j) for x,y,j in hyp]
            if induct:
                for name,field in zip(names,fields):
                    if field==sort:premises.append((sub(na,{variable:var(name)}),sub(nz,{variable:var(name)}),len(premises)))
            proof=state_proof(objects,sub(na,binding),sub(nz,binding),local,premises,depth+1,serial,aliases,scalar,lemma_attempts,strengthen)
            cases.append(dict(bindings=names,proof=proof))
        return trans(pa,{('Induction' if induct else 'Cases'):dict(variable=variable,**{'from':na,'to':nz},cases=cases)},{'Sym':pz})
    raise ValueError('unclosed contract state goal '+str((na,nz))[:600])

def author(compiler,source,directory,bodies=None,source_evidence=None):
    compiler=str(Path(compiler).resolve());source=str(Path(source).resolve())
    directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=True)
    options=["--core"] if Path(source).suffix==".json" else []
    if source_evidence:options += ['--contract-proofs',str(Path(source_evidence).resolve())]
    if bodies:options += ['--refinement-bodies',str(Path(bodies).resolve())]
    export=directory/'obligations.json'
    subprocess.run([compiler,'emit-contract-obligations',source,'-o',str(export),*options],check=True,capture_output=True,text=True)
    goals=json.loads(export.read_text())
    with ProofSession(compiler,source,options,goals['source_sha256']) as session:
        return author_obligations(compiler,source,directory,bodies,options,goals,session)

class ProofSession:
    """Reuse source derivation, never a previous proof verdict."""
    def __init__(self,compiler,source,options,expected):
        self.arguments=[compiler,'check-contract-proof-stream',source,*options]
        self.expected=expected;self.process=None
    def __enter__(self):
        self.process=subprocess.Popen(self.arguments,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        try:
            ready=self.read()
            if ready!={'status':'ready','source_sha256':self.expected}:raise ValueError('proof session source identity differs from export')
        except BaseException:
            self.__exit__(None,None,None);raise
        return self
    def read(self):
        line=self.process.stdout.readline()
        if not line:raise ValueError('proof checker ended: '+self.process.stderr.read()[-1200:])
        return json.loads(line)
    def check(self,name,proof,bundle):
        self.process.stdin.write(json.dumps(dict(name=name,proof=proof,knowledge=bundle),separators=(',',':'))+'\n')
        self.process.stdin.flush();answer=self.read()
        if answer.get('status') not in ('checked','rejected'):raise ValueError('unknown proof checker verdict')
        # Transport/schema rejection may precede decoding the obligation name.
        # It is a failed proposal, never a checked verdict or a reusable fact.
        if answer.get('name')!=name and not(answer['status']=='rejected' and 'name'not in answer and isinstance(answer.get('error'),str)):
            raise ValueError('proof checker response obligation differs')
        return answer
    def __exit__(self,*unused):
        if self.process is not None:
            self.process.stdin.close();self.process.wait()
            self.process.stdout.close();self.process.stderr.close()


def author_obligations(compiler,source,directory,bodies,options,goals,session):
    pure_objects={};state_objects=dict((goals['state'] or {}).get('objects',{}));pure_roots=[];state_roots=[]
    proofs={};state_proofs={};names={};installed=Store(Path(__file__).resolve().parents[1])
    def check(g,proof,bundle=None):
        path=directory/'trial.json';path.write_text(json.dumps(dict(proof=proof,knowledge=bundle)))
        answer=session.check(g['name'],proof,bundle)
        if answer['status']=='rejected':(directory/"last-check-error.txt").write_text(answer['error'])
        return answer['status']=='checked'
    for g in goals['pure']:
        proof=next((p for p in pure_proposals(g) if check(g,p)),None);dependencies=[]
        if proof is None:
            from producers.owned_fold_contracts import proposals as owned_proposals
            for candidate,bundle in owned_proposals(g,installed,goals['definition_context']):
                if check(g,candidate,bundle):
                    proof=candidate;dependencies=bundle['roots'];pure_objects.update(bundle['objects']);break
        if proof is None:
            from producers.semantic_observations import proposals
            for candidate,bundle in proposals(g,installed,goals['definition_context']):
                if check(g,candidate,bundle):
                    proof=candidate;dependencies=bundle['roots'];pure_objects.update(bundle['objects']);break
        if proof is None:
            for candidate,bundle in rewrite_proposals(g,installed):
                if check(g,candidate,bundle):
                    proof=candidate;dependencies=bundle['roots'];pure_objects.update(bundle['objects']);break
        if proof is None:raise ValueError('no checked proof for '+g['name'])
        law=dict(schema=1,semantics=proof_semantics(proof),params=g['params'],conditions=g['conditions'],**g['goal'],proof=proof,dependencies=dependencies,definition_context=context_for(goals['definition_context'],g))
        obj=semantic_entry(law);i=identity(obj);pure_objects[i]=obj;pure_roots.append(i);names['contract.'+g['name']]=i
        proofs[g['name']]={'Use':dict(law=i,arguments={n:dict(sort=t,node={'Free':n}) for n,t in g['params'].items()},premises=[{'Hypothesis':j} for j in range(len(g['conditions']))])}
    def add(declaration):
        from producers.proof_composition import balance_transitivity
        if 'Theorem' in declaration:
            declaration={**declaration,'Theorem':{**declaration['Theorem'],'proof':balance_transitivity(declaration['Theorem']['proof'])}}
        d=next(iter(declaration.values()));deps=references(declaration);pending=list(deps)
        while pending:
            for dep in state_objects[pending.pop()]['dependencies']:
                if dep not in deps:deps.add(dep);pending.append(dep)
        metadata=dict(parameters=dict(d.get('params',[])))
        if 'Theorem' in declaration:metadata['conditions']=d['conditions']
        if 'Function' in declaration:metadata['result']=d['result']
        obj=entry('theorem' if 'Theorem' in declaration else 'definition',MATH,dict(declaration=declaration),deps,**metadata);i=identity(obj);state_objects[i]=obj;return i
    from producers.tree_proofs import Tactic as TypedTactic
    from producers.scalar_tactic import Scalar
    typed=TypedTactic(state_objects,add)
    scalar=Scalar(add,typed.sort,lambda term,env:term,compiler=compiler)
    # Alpha-equivalent generated traversals still have independent canonical IDs.
    # Propose ordinary induction theorems between them; never identify their
    # meanings merely from names or syntax in the trusted kernel.
    from producers.equational import alpha
    aliases={};classes={};pending={i:o['payload']['declaration']['Function'] for i,o in state_objects.items() if 'Function' in o['payload']['declaration']}
    def canonical_calls(x):
        if isinstance(x,list):return [canonical_calls(v) for v in x]
        if not isinstance(x,dict):return x
        return {k:(aliases[v][0] if k=='function' and v in aliases else canonical_calls(v)) for k,v in x.items()}
    while pending:
        ready=[i for i,d in pending.items() if not (references(d)&pending.keys())]
        if not ready:break
        for i in ready:
            d=pending.pop(i);params=[(f'contract_alias_{j}',t) for j,(_,t) in enumerate(d['params'])]
            body=alpha(canonical_calls(sub(d['body'],{n:var(m) for (n,_),(m,_) in zip(d['params'],params)})))
            key=json.dumps([params,d['result'],d['recursive'],body],sort_keys=True)
            if key not in classes:classes[key]=i;continue
            target=classes[key];args=[var(n) for n,_ in params]
            a={'Call':dict(function=i,arguments=args)};z={'Call':dict(function=target,arguments=args)}
            (directory/'progress.json').write_text(json.dumps(dict(phase="traversal-equivalence",function=i,target=target)))
            try:proof=state_proof(state_objects,a,z,dict(params),aliases=aliases,scalar=scalar)
            except ValueError:continue
            theorem=add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
            aliases[i]=(target,theorem)
    # Propose reflexivity for homogeneous Boolean relations over data. This is
    # search, not recognition authority: induction must prove each candidate.
    for i,obj in list(state_objects.items()):
        d=obj['payload']['declaration'].get('Function')
        if i in aliases or not d or d['result']!='Bool' or len(d['params'])!=2:continue
        sort=d['params'][0][1]
        if sort!=d['params'][1][1] or not isinstance(sort,dict) or 'Data' not in sort:continue
        params=[('contract_reflexive',sort)];argument=var(params[0][0])
        a={'Call':dict(function=i,arguments=[argument,argument])};z={'Bool':True}
        try:proof=state_proof(state_objects,a,z,dict(params),aliases=aliases,scalar=scalar)
        except ValueError:continue
        theorem=add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
        aliases[i]=(None,theorem)
    from producers.owned_fold_state import propose as owned_state_proposals
    aliases.update(owned_state_proposals(state_objects,add,state_proof))
    (directory/'derived-aliases.json').write_text(json.dumps(aliases,sort_keys=True))
    for number,g in enumerate((goals['state'] or {}).get('obligations',[])):
        (directory/'progress.json').write_text(json.dumps(dict(phase='state-obligation',name=g['name'])))
        from producers.point_delta import free_variables
        a,z=g['goal']['from'],g['goal']['to'];all_conditions=g['conditions']
        data_names={n for n,t in g['params'] if isinstance(t,dict) and 'Data' in t}
        subsets=[list(range(len(all_conditions))),*[[i for i,c in enumerate(all_conditions) if variable not in (free_variables(c['from'])|free_variables(c['to']))] for variable,_ in g['params'] if variable in data_names],[]]
        subsets=list(dict.fromkeys(tuple(indices) for indices in subsets))
        subsets=[list(indices) for indices in subsets]
        success=False;errors=[]
        direct=next((p for p in [convert(a,z),*[{'Hypothesis':i} for i in range(len(all_conditions))]] if check(g,p)),None)
        ordered=[subsets[0]] if direct is not None else [*subsets[1:],subsets[0]]
        for attempt,indices in enumerate(ordered):
            (directory/'progress.json').write_text(json.dumps(dict(phase='state-obligation',name=g['name'],conditions=indices)))
            conditions=[all_conditions[i] for i in indices];hyp=[(c['from'],c['to'],i) for i,c in enumerate(conditions)]
            try:
                proof=direct if direct is not None else state_proof(state_objects,a,z,dict(g['params']),hyp,aliases=aliases if indices else {},scalar=scalar)
            except ValueError as error:errors.append(str(error));continue
            i=add({'Theorem':dict(params=g['params'],conditions=conditions,**g['goal'],proof=proof)})
            trial=Store.publish(directory/'trials'/f'{number}-{attempt}',state_objects.values())
            use={'Use':dict(theorem=i,arguments=[var(n) for n,_ in g['params']],premises=[{'Hypothesis':j} for j in indices])}
            if check(g,use,trial.bundle([i])):
                state_roots.append(i);names['contract.'+g['name']]=i;state_proofs[g['name']]=use;success=True;break
            state_objects.pop(i)
        if not success:
            from producers.conditional_induction import guarded_goal,apply_guarded
            guarded=guarded_goal(g)
            if guarded is not None:
                guard,guard_proof,statement=guarded
                try:
                    proof=state_proof(state_objects,statement,z,dict(g['params']),aliases=aliases,scalar=scalar)
                    i=add({'Theorem':dict(params=g['params'],conditions=[],**{'from':statement,'to':z},proof=proof)})
                    trial=Store.publish(directory/'trials'/f'{number}-guarded',state_objects.values())
                    use=apply_guarded(g,guard,guard_proof,i)
                    if check(g,use,trial.bundle([i])):
                        state_roots.append(i);names['contract.'+g['name']]=i;state_proofs[g['name']]=use;success=True
                    else:state_objects.pop(i)
                except ValueError as error:errors.append(str(error))
        if not success:raise ValueError('no checked state proof for '+g['name']+': '+'; '.join(errors)[-1200:])
    store=Store.publish(directory,[*pure_objects.values(),*state_objects.values()],names)
    evidence=dict(schema=1,semantics=goals['semantics'],source_sha256=goals['source_sha256'],proofs=proofs,state_proofs=state_proofs,knowledge=store.bundle(pure_roots) if pure_roots else None,state_knowledge=store.bundle(state_roots) if state_roots else None)
    (directory/'progress.json').write_text(json.dumps(dict(phase='proofs-replayed',pure=len(proofs),state=len(state_proofs))))
    target=directory/'evidence.json';target.write_text(json.dumps(evidence,separators=(',',':'))+'\n')
    if not bodies:subprocess.run([compiler,'check-contracts',source,'--contract-proofs',str(target),*(['--core'] if Path(source).suffix=='.json' else [])],check=True,capture_output=True,text=True)
    return evidence,store

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source');p.add_argument('output');p.add_argument('--compiler',required=True);p.add_argument('--bodies');p.add_argument('--source-evidence');a=p.parse_args()
    author(a.compiler,a.source,a.output,a.bodies,a.source_evidence)
    print('Checked contract evidence and canonical entries:',a.output)
if __name__=='__main__':main()
