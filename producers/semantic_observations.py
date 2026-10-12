"""Binder-safe, untrusted contextual theorem application.

Construct ordinary congruence/extensionality proofs for observations under
arbitrary lambda scopes. Returned terms and proofs require independent replay.
"""
import copy
from producers.beta_specialization15 import beta_normalize
from ink_planner.semantic_search import children,match,substitute

def opened(term,scope,depth=0):
    result=copy.deepcopy(term);node=result['node']
    if isinstance(node,dict):
        if 'Bound'in node and node['Bound']>=depth:
            index=node['Bound']-depth
            if index>=len(scope):raise ValueError('observation proof has an unbound index')
            name,sort=scope[-1-index];return dict(sort=sort,node={'Free':name})
        if 'Lambda'in node:node['Lambda']=opened(node['Lambda'],scope,depth+1)
        elif 'Op'in node:node['Op'][1]=[opened(x,scope,depth)for x in node['Op'][1]]
        elif 'Cons'in node:node['Cons']=[opened(x,scope,depth)for x in node['Cons']]
    return result

def preprocess(term):
    """Propose beta and fixed structural equality reductions, with no laws."""
    def walk(t,depth=0):
        if depth>128:raise ValueError('observation normalization depth')
        t=copy.deepcopy(t);node=t['node']
        if isinstance(node,dict):
            if 'Lambda'in node:node['Lambda']=walk(node['Lambda'],depth+1)
            if 'Cons'in node:node['Cons']=[walk(x,depth+1)for x in node['Cons']]
            if 'Op'in node:
                name,args=node['Op'];args=[walk(x,depth+1)for x in args];node['Op'][1]=args
                if name in ('binary:==','binary:!=')and len(args)==2:
                    a,b=args
                    if isinstance(a['node'],dict)and isinstance(b['node'],dict)and 'Bool'in a['node']and 'Bool'in b['node']:
                        return dict(sort=t['sort'],node={'Bool':(a['node']['Bool']==b['node']['Bool'])==(name=='binary:==')})
                    if isinstance(a['node'],dict)and 'Cons'in a['node']and isinstance(b['node'],dict)and 'Cons'in b['node']:
                        x,xt=a['node']['Cons'];y,yt=b['node']['Cons']
                        if xt['node']=='Nil'and yt['node']=='Nil':
                            equal=dict(sort={'Value':'Bool'},node={'Op':['value:equal',[x,y]]})
                            return equal if name=='binary:=='else dict(sort=t['sort'],node={'Op':['binary:==',[equal,dict(sort=t['sort'],node={'Bool':False})]]})
                    if a==b and a['sort']!={'Value':'F32'}:
                        return dict(sort=t['sort'],node={'Bool':name=='binary:=='})
                if name=='binary:&&'and len(args)==2:
                    if args[0]['node']=={'Bool':True}:return args[1]
                    if args[1]['node']=={'Bool':True}:return args[0]
        return t
    return walk(beta_normalize(term))

def contextual_rewrite(term,rules,parameters):
    used=set();serial=[0]
    def visit(t,scope=(),depth=0):
        if depth>128:raise ValueError('observation rewriting depth')
        for ident,law in rules:
            args={}
            if match(law['from'],t,law['params'],args)and set(args)==set(law['params']):
                updated=substitute(law['to'],args)
                if updated==t:continue
                used.add(ident)
                return updated,{'Use':dict(law=ident,arguments={n:opened(v,scope)for n,v in args.items()},premises=['Normalize']*len(law['conditions']))}
        node=t['node'];updated=copy.deepcopy(t)
        if isinstance(node,dict)and 'Lambda'in node:
            name='__observation_'+str(serial[0]);serial[0]+=1
            while name in parameters or name in dict(scope):name+='_' 
            value,proof=visit(node['Lambda'],(*scope,(name,t['sort']['Arrow'][0])),depth+1)
            updated['node']['Lambda']=value
            return updated,'Normalize'if value==node['Lambda']else {'Forall':dict(parameter=name,body=proof)}
        values=[];proofs=[]
        for child in children(t):
            value,proof=visit(child,scope,depth+1);values.append(value);proofs.append(proof)
        if isinstance(node,dict):
            if 'Op'in node:updated['node']['Op'][1]=values
            if 'Cons'in node:updated['node']['Cons']=values
        return updated,'Normalize'if updated==t else {'Congruence':proofs}
    result,proof=visit(term)
    return result,proof,used

def proposals(goal,store,context,rounds=8):
    """Bounded observation search under binders, using snapshot-owned laws.

    Beta/structural conversions, template instantiation and every contextual
    application are proposals. The caller must replay the complete certificate.
    """
    from ink_knowledge import semantic_entry,identity
    from ink_knowledge.law_templates import generate
    from ink_planner.semantic_search import positions,key
    definitions=context['definitions']
    core={'program':dict(functions=[dict(name=n,params=d['definition']['params'],result=d['definition']['result'])for n,d in definitions.items()],records=context['records'],enums=context['enums'])}
    bodies={n:d['definition']['body']for n,d in definitions.items()}
    current=goal['goal']['from'];proof='Normalize';objects={};roots=set();cache={};seen=set()
    def closure(ids):
        import tempfile
        from ink_knowledge import Store
        pending=list(ids);chosen={}
        while pending:
            ident=pending.pop()
            if ident in chosen:continue
            obj=objects.get(ident)or store.object(ident);chosen[ident]=obj;pending.extend(obj['dependencies'])
        with tempfile.TemporaryDirectory(prefix='ink-observation-proof-')as directory:
            return Store.publish(directory,chosen.values()).bundle(ids)
    # Retain exact original facts: preprocessing never changes the goal's scope.
    for _ in range(rounds):
        normalized=preprocess(current)
        if normalized!=current:
            proof={'Trans':dict(middle=current,left=proof,right='Normalize')};current=normalized
        signature=key(current)
        if signature in seen:return
        seen.add(signature)
        # Whole source context is used only to bind nominal definitions. Templates
        # are inferred from the actual observation, including its lambda sites.
        extra,_=generate(store,dict(functions={**bodies,'__contract_observation':current}),core);objects.update(extra)
        rules=[]
        for _,target in positions(current):
            node=target['node']
            if not isinstance(node,dict)or 'Op'not in node:continue
            op=node['Op'][0];query=(key(target['sort']),op)
            if query not in cache:
                rows=[];after=None
                while len(rows)<1024:
                    page=store.query(kind='rewrite',semantics='ink-conditional-laws-v1',result=target['sort'],operation=op,after=after,limit=128)
                    for ident in page:
                        obj=store.object(ident);head=obj['payload']['from']['node']
                        if isinstance(head,dict)and head.get('Op',[None])[0]==op:rows.append((ident,obj))
                    if len(page)<128:break
                    after=page[-1]
                cache[query]=rows
            for ident,obj in cache[query]:objects[ident]=obj
        for ident,obj in objects.items():
            if obj['kind']=='rewrite'and obj['semantics']=='ink-conditional-laws-v1':
                law=obj['payload']
                if not law.get('types')and not law.get('assumptions'):rules.append((ident,law))
        # Prefer strict structural reductions; this is search policy only.
        def size(t):return 1+sum(size(c)for c in children(t))
        rules=[(i,l)for i,l in rules if size(l['to'])<size(l['from'])and not l['conditions']]
        updated,step,used=contextual_rewrite(current,rules,goal['params'])
        if updated==current:return
        roots.update(used);proof={'Trans':dict(middle=current,left=proof,right=step)};current=updated
        normalized=preprocess(current)
        terminal='Normalize'if normalized==current else {'Trans':dict(middle=normalized,left='Normalize',right='Normalize')}
        yield {'Trans':dict(middle=current,left=proof,right=terminal)},closure(roots)
