"""Untrusted incremental point-query proposals and ordinary induction proofs.

Repairs fixed point projections across parameter-key histories; unsupported changes refresh.
The core knows no query/update pattern and rechecks all future-state obligations.
"""
from producers.action_replacement import var,call,cons,convert,trans
from producers.cache_maintenance import variables

def choice(c,t,f):return {'If':dict(condition=c,on_true=t,on_false=f)}
def binary(n,a,b):return {'Binary':dict(op=n,left=a,right=b)}
def match(t,branches):return {'Match':dict(scrutinee=t,branches=[dict(bindings=ns,body=b) for ns,b in branches])}
def free_variables(t,bound=frozenset()):
    if isinstance(t,list):return set().union(*(free_variables(x,bound) for x in t)) if t else set()
    if not isinstance(t,dict):return set()
    if set(t)=={'Var'}:return set() if t['Var'] in bound else {t['Var']}
    if 'Match'in t:
        x=t['Match'];return free_variables(x['scrutinee'],bound)|set().union(*(free_variables(b['body'],bound|set(b['bindings'])) for b in x['branches']))
    return set().union(*(free_variables(x,bound) for x in t.values())) if t else set()
def sub(t,m):
    if isinstance(t,list):return [sub(x,m) for x in t]
    if not isinstance(t,dict):return t
    if set(t)=={'Var'}:return m.get(t['Var'],t)
    if 'Match' in t:
        x=t['Match'];branches=[]
        for b in x['branches']:
            bindings=list(b['bindings']);local={k:v for k,v in m.items() if k not in bindings};body=b['body']
            captures=set().union(*(free_variables(v) for v in local.values())) if local else set()
            occupied=variables(body)|captures|set(local)|set(bindings);renames={}
            for i,n in enumerate(bindings):
                if n not in captures:continue
                serial=0
                while True:
                    fresh=n[:40]+'_proposal_'+str(serial);serial+=1
                    if fresh not in occupied:break
                occupied.add(fresh);bindings[i]=fresh;renames[n]=var(fresh)
            if renames:body=sub(body,renames)
            branches.append((bindings,sub(body,local)))
        return match(sub(x['scrutinee'],m),branches)
    return {k:sub(v,m) for k,v in t.items()}
def replace(t,a,z):
    if t==a:return z
    if isinstance(t,list):return [replace(x,a,z) for x in t]
    if isinstance(t,dict):return {k:replace(x,a,z) for k,x in t.items()}
    return t

def normal(t,objects,depth=0,opaque=(),*,blocked=(),eager=()):
    """Authoring computation only. Every proposed reduction is checked by Convert."""
    if depth>96:raise ValueError('point delta producer depth budget')
    recur=lambda t:normal(t,objects,depth+1,opaque,blocked=blocked,eager=eager)
    if not isinstance(t,dict):return t
    if 'Call' in t:
        x=t['Call'];args=[recur(a) for a in x['arguments']];decl=objects[x['function']]['payload']['declaration']
        if x['function'] in opaque or 'AbstractFunction' in decl:return call(x['function'],args)
        if x['function'] in blocked and not (x['function']in eager and any('Construct'in a for a in args)):return call(x['function'],args)
        f=decl['Function']
        if f['recursive'] is not None and 'Construct' not in args[f['recursive']]:return call(x['function'],args)
        body=f['body']
        def selfcalls(x):
            if isinstance(x,dict):
                if 'SelfCall' in x:return call(t['Call']['function'],[selfcalls(a) for a in x['SelfCall']])
                return {k:selfcalls(v) for k,v in x.items()}
            if isinstance(x,list):return [selfcalls(v) for v in x]
            return x
        return recur(sub(selfcalls(body),dict(zip([n for n,_ in f['params']],args))))
    if 'If' in t:
        x=t['If'];c=recur(x['condition'])
        if 'Bool' in c:return recur(x['on_true' if c['Bool'] else 'on_false'])
        return choice(c,recur(x['on_true']),recur(x['on_false']))
    if 'Construct' in t:
        x=t['Construct'];return cons(x['datatype'],x['constructor'],[recur(a) for a in x['arguments']])
    if 'Match' in t:
        x=t['Match'];scrutinee=recur(x['scrutinee'])
        if 'Construct' in scrutinee:
            c=scrutinee['Construct'];b=x['branches'][c['constructor']];return recur(sub(b['body'],dict(zip(b['bindings'],c['arguments']))))
        branches=[]
        for b in x['branches']:
            bindings=list(b['bindings']);used=free_variables(b['body']);occupied=set(used)
            for i,name in enumerate(bindings):
                if name in used:continue
                serial=0
                while True:
                    fresh='unused_binding_'+str(i)+'_'+str(serial);serial+=1
                    if fresh not in occupied:break
                bindings[i]=fresh;occupied.add(fresh)
            branches.append((bindings,b['body']))
        return match(scrutinee,branches)
    if 'Binary' in t:
        x=t['Binary'];a,z=recur(x['left']),recur(x['right'])
        if 'U64' in a and 'U64' in z:
            av,zv=a['U64'],z['U64'];op=x['op'];return {'Bool':{'==':av==zv,'!=':av!=zv,'<':av<zv,'<=':av<=zv,'>':av>zv,'>=':av>=zv}[op]} if op in ['==','!=','<','<=','>','>='] else {'U64':{'+':av+zv,'-':av-zv,'*':av*zv,'&':av&zv}[op]%(1<<64)}
        if 'Bool'in a and 'Bool'in z:
            av,zv=a['Bool'],z['Bool'];op=x['op']
            return {'Bool':{'&&':av and zv,'||':av or zv,'==':av==zv,'!=':av!=zv}[op]}
        return binary(x['op'],a,z)
    return t

def lift(eq,context):return {'Substitute':dict(variable='delta_hole',context=context,equality=eq)}
def equality(a,z,objects,hyp=None,facts=()):
    facts=tuple((normal(left,objects),normal(right,objects),index) for left,right,index in facts)
    def simplify(t):
        current=normal(t,objects);proof=convert(t,current)
        for _ in range(16):
            changed=False
            for left,right,index in facts:
                rewritten=replace(current,left,right)
                if rewritten!=current:
                    context=replace(current,left,var('delta_hole'))
                    following=normal(rewritten,objects)
                    proof=trans(proof,lift(index if isinstance(index,dict) else {'Hypothesis':index},context),convert(rewritten,following))
                    current=following;changed=True
            if not changed:return current,proof
        raise ValueError('point delta tactic rewrite budget')
    na,pa=simplify(a);nz,pz=simplify(z)
    from action_replacement import alpha_normal
    if alpha_normal(na)==alpha_normal(nz):return trans(pa,convert(na,nz),{'Sym':pz})
    if hyp:
        ha,hz,index=hyp;ha,ha_proof=simplify(ha);hz,hz_proof=simplify(hz)
        inherited=trans({'Sym':ha_proof},index if isinstance(index,dict) else {'Hypothesis':index},hz_proof)
        context=replace(na,ha,var('delta_hole'));rewritten=replace(na,ha,hz)
        if normal(rewritten,objects)==nz:return trans(pa,lift(inherited,context),convert(rewritten,nz),{'Sym':pz})
    raise ValueError('point delta proof tactic cannot establish this equation: '+str((na,nz)))

def setup(model,cache,add,objects):
    from producers.point_projection_delta import setup as projected_setup
    return projected_setup(model,cache,add,objects)
