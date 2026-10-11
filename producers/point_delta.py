"""Untrusted incremental point-query proposals and ordinary induction proofs.

Repairs fixed point projections across parameter-key histories; unsupported changes refresh.
The core knows no query/update pattern and rechecks all future-state obligations.
"""
from action_replacement import var,call,cons,convert,trans
from cache_maintenance import variables

def choice(c,t,f):return {'If':dict(condition=c,on_true=t,on_false=f)}
def binary(n,a,b):return {'Binary':dict(op=n,left=a,right=b)}
def match(t,branches):return {'Match':dict(scrutinee=t,branches=[dict(bindings=ns,body=b) for ns,b in branches])}
def sub(t,m):
    if isinstance(t,list):return [sub(x,m) for x in t]
    if not isinstance(t,dict):return t
    if set(t)=={'Var'}:return m.get(t['Var'],t)
    # Capture avoidance is necessary even for producer-generated binders:
    # normalising a helper can substitute a caller tail with the same name.
    if 'Match' in t:
        def names(x):
            if isinstance(x,list):return set().union(*(names(v) for v in x))
            if not isinstance(x,dict):return set()
            found={x['Var']} if 'Var'in x else set()
            if 'bindings'in x:found.update(x['bindings'])
            return found|set().union(*(names(v)for v in x.values()))
        x=t['Match'];branches=[];used=names(t)|names(list(m.values()))|set(m)
        for b in x['branches']:
            bindings=list(b['bindings']);body=b['body'];local={k:v for k,v in m.items()if k not in bindings}
            captures=names(list(local.values()))
            for index,name in enumerate(bindings):
                if name not in captures:continue
                serial=0
                while f'delta_bound_{serial}'in used:serial+=1
                fresh=f'delta_bound_{serial}';used.add(fresh)
                body=sub(body,{name:var(fresh)});bindings[index]=fresh
            branches.append((bindings,sub(body,local)))
        return match(sub(x['scrutinee'],m),branches)
    return {k:sub(v,m) for k,v in t.items()}
def replace(t,a,z):
    if t==a:return z
    if isinstance(t,list):return [replace(x,a,z) for x in t]
    if isinstance(t,dict):return {k:replace(x,a,z) for k,x in t.items()}
    return t

def normal(t,objects,depth=0):
    """Authoring computation only. Every proposed reduction is checked by Convert."""
    if depth>96:raise ValueError('point delta producer depth budget')
    recur=lambda t:normal(t,objects,depth+1)
    if not isinstance(t,dict):return t
    if 'Call' in t:
        x=t['Call'];args=[recur(a) for a in x['arguments']];declaration=objects[x['function']]['payload']['declaration']
        if 'AbstractFunction'in declaration:return call(x['function'],args)
        f=declaration['Function']
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
        return match(scrutinee,[(b['bindings'],b['body']) for b in x['branches']])
    if 'Binary' in t:
        x=t['Binary'];a,z=recur(x['left']),recur(x['right'])
        if 'U64' in a and 'U64' in z:
            av,zv=a['U64'],z['U64'];op=x['op'];return {'Bool':{'==':av==zv,'!=':av!=zv,'<':av<zv,'<=':av<=zv,'>':av>zv,'>=':av>=zv}[op]} if op in ['==','!=','<','<=','>','>='] else {'U64':{'+':av+zv,'-':av-zv,'*':av*zv,'&':av&zv}[op]%(1<<64)}
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
