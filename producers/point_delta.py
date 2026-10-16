"""Untrusted incremental point-query proposals and ordinary induction proofs.

Repairs fixed point projections across parameter-key histories; unsupported changes refresh.
The core knows no query/update pattern and rechecks all future-state obligations.
"""
from producers.action_replacement import var,call,cons,convert,trans
from producers.cache_maintenance import variables
from producers.fixed_f32 import evaluate as fixed_f32
import json

def choice(c,t,f):return {'If':dict(condition=c,on_true=t,on_false=f)}
def binary(n,a,b):return {'Binary':dict(op=n,left=a,right=b)}
def match(t,branches):return {'Match':dict(scrutinee=t,branches=[dict(bindings=ns,body=b) for ns,b in branches])}

class _BindingFacts:
    """Bounded immutable syntax summaries for one synchronous authoring walk.

    Keep exact objects alive on a cache hit: Python identities never survive this
    walk or authorize a proof. Charge a conservative unshared tree size as well
    as summary metadata, so retaining a small key cannot retain an unbounded
    temporary tree. Cache exhaustion preserves ordinary traversal.
    """
    MAX_ENTRIES = 4096
    MAX_BYTES = 2_000_000
    MAX_ENTRY_BYTES = 8192

    def __init__(self):
        self.entries = {}
        self.bytes = 0

    def of(self, value):
        # During this walk the root keeps every borrowed descendant alive.
        # Large shared subtrees therefore need only bounded summary metadata;
        # no input object is retained after this walk merely for its identity.
        return self._of(value, {}, [0])

    def _of(self, value, local, local_bytes):
        if not isinstance(value, (dict, list)):
            size = 64 + (4 * len(value) if isinstance(value, str) else 64)
            return frozenset(), frozenset(), min(size, self.MAX_ENTRY_BYTES + 1)
        found = self.entries.get(id(value))
        if found is not None and found[0] is value:
            return found[1]
        found = local.get(id(value))
        if found is not None:
            return found
        free, bound = set(), set()
        size = 128 + 96 * len(value)
        def add(child, subtract=()):
            nonlocal size
            names, bindings, weight = self._of(child, local, local_bytes)
            free.update(names - set(subtract)); bound.update(bindings)
            size = min(self.MAX_ENTRY_BYTES + 1, size + weight)
        if isinstance(value, dict) and set(value) == {'Var'}:
            free.add(value['Var'])
            size += 64 + 4 * len(value['Var'])
        elif isinstance(value, dict) and 'Match' in value:
            node = value['Match']; add(node['scrutinee'])
            for branch in node['branches']:
                names = branch['bindings']; bound.update(names)
                size += sum(64 + 4 * len(name) for name in names)
                add(branch['body'], names)
        else:
            if isinstance(value, dict):
                size += sum(64 + 4 * len(key) for key in value)
                children = value.values()
            else:
                children = value
            for child in children:
                add(child)
        result = frozenset(free), frozenset(bound), min(size, self.MAX_ENTRY_BYTES + 1)
        metadata = 1024 + sum(128 + 4 * len(name) for name in free | bound)
        weight = result[2] + metadata
        if (size <= self.MAX_ENTRY_BYTES and len(self.entries) < self.MAX_ENTRIES
                and self.bytes + weight <= self.MAX_BYTES):
            self.entries[id(value)] = value, result
            self.bytes += weight
        if len(local) < self.MAX_ENTRIES and local_bytes[0] + metadata <= self.MAX_BYTES:
            local[id(value)] = result
            local_bytes[0] += metadata
        return result

def free_variables(t,bound=frozenset()):
    return set(_BindingFacts().of(t)[0]) - set(bound)
def sub(t,m):
    return _sub(t,m,_BindingFacts())
def _sub(t,m,facts):
    if isinstance(t,list):return [_sub(x,m,facts) for x in t]
    if not isinstance(t,dict):return t
    if set(t)=={'Var'}:return m.get(t['Var'],t)
    if 'Match' in t:
        x=t['Match'];branches=[]
        for b in x['branches']:
            bindings=list(b['bindings']);local={k:v for k,v in m.items() if k not in bindings};body=b['body']
            # The kernel also forbids lexical shadowing of an outer binder by
            # binders inside a substituted value. Bound names in arguments must
            # therefore be avoided even when they cannot capture a free value.
            captures=set().union(*(facts.of(v)[0]|facts.of(v)[1] for v in local.values())) if local else set()
            free,bound,_=facts.of(body)
            occupied=set(free)|set(bound)|captures|set(local)|set(bindings);renames={}
            for i,n in enumerate(bindings):
                if n not in captures:continue
                serial=0
                while True:
                    fresh=n[:40]+'_proposal_'+str(serial);serial+=1
                    if fresh not in occupied:break
                occupied.add(fresh);bindings[i]=fresh;renames[n]=var(fresh)
            if renames:body=_sub(body,renames,facts)
            branches.append((bindings,_sub(body,local,facts)))
        return match(_sub(x['scrutinee'],m,facts),branches)
    return {k:_sub(v,m,facts) for k,v in t.items()}
def replace(t,a,z):
    if t==a:return z
    if isinstance(t,list):return [replace(x,a,z) for x in t]
    if isinstance(t,dict):return {k:replace(x,a,z) for k,x in t.items()}
    return t

def binding_names(t):
    return set(_BindingFacts().of(t)[1])

class _CallCache:
    """Exact invocation-local authoring results, never proof verdicts.

    Definitions and modes are fixed during one synchronous normalization. Do
    not carry entries into another call, even if it uses the same registry.
    Preserve JSON container order and return fresh containers on a hit.
    """
    MAX_ENTRIES=256
    MAX_BYTES=2_000_000
    MAX_ENTRY_BYTES=8192
    WARMUP_CALLS=32

    def __init__(self):
        self.entries={};self.bytes=0;self.calls=0;self.structural={}

    @classmethod
    def encode(cls,value):
        pending=[value];nodes=0;characters=0
        while pending:
            item=pending.pop();nodes+=1
            if nodes>128:return None
            if type(item)is dict:
                if any(type(k)is not str for k in item):return None
                pending.extend(item.keys());pending.extend(item.values())
            elif type(item)is list:pending.extend(item)
            elif type(item)is str:characters+=len(item)
            elif type(item)is int:
                if item.bit_length()>256:return None
            elif item is not None and type(item)is not bool:return None
            if characters>cls.MAX_ENTRY_BYTES:return None
        encoded=json.dumps(value,separators=(',',':'))
        return encoded if len(encoded)<=cls.MAX_ENTRY_BYTES else None

    def key(self,function,args,depth):
        # Depth matters: a result established with more remaining unfolding
        # work must not let a deeper occurrence evade the existing limit.
        return self.encode([function,args,depth])

    def get(self,key):
        return self.entries.get(key) if key is not None else None

    def put(self,key,value):
        if key is None or key in self.entries or len(self.entries)>=self.MAX_ENTRIES:return
        encoded=self.encode(value)
        if encoded is None or self.bytes+len(key)+len(encoded)>self.MAX_BYTES:return
        self.entries[key]=encoded;self.bytes+=len(key)+len(encoded)


def normal(t,objects,depth=0,opaque=(),*,blocked=(),eager=(),heads=()):
    """Authoring computation only. Every proposed reduction is checked by Convert."""
    return _normal(t,objects,depth,opaque,blocked,eager,heads,_CallCache())


def _constructor_head(term,objects,heads,depth):
    original=term;seen=set()
    while isinstance(term,dict) and 'Call' in term:
        invocation=term['Call'];key=invocation['function']
        if invocation['arguments'] or key not in heads:return original
        if key in seen or depth+len(seen)>96:raise ValueError('constructor head depth/cycle budget')
        seen.add(key);f=objects[key]['payload']['declaration'].get('Function')
        if not f or f['params'] or f['recursive'] is not None:return original
        term=f['body']
    return term if isinstance(term,dict) and 'Construct' in term else original


def _normal(t,objects,depth,opaque,blocked,eager,heads,cache):
    if depth>96:raise ValueError('point delta producer depth budget')
    recur=lambda t:_normal(t,objects,depth+1,opaque,blocked,eager,heads,cache)
    if not isinstance(t,dict):return t
    if 'Call' in t:
        x=t['Call'];args=[recur(a) for a in x['arguments']];decl=objects[x['function']]['payload']['declaration']
        if x['function'] in opaque or 'AbstractFunction' in decl:return call(x['function'],args)
        if x['function'] in blocked and not (x['function']in eager and any('Construct'in a for a in args)):return call(x['function'],args)
        f=decl['Function']
        if f['recursive'] is not None:
            i=f['recursive'];exposed=_constructor_head(args[i],objects,heads,depth+1)
            if exposed is not args[i]:
                # Constructor aliases may drive recursive data operations.
                # Acyclic owner gates stay explicit for their universal case
                # lemmas, rather than expanding a whole application context.
                if x['function'] not in cache.structural:
                    pending=[f['body']];found=False
                    while pending:
                        value=pending.pop()
                        if isinstance(value,dict):
                            if 'SelfCall' in value:found=True;break
                            pending.extend(value.values())
                        elif isinstance(value,list):pending.extend(value)
                    cache.structural[x['function']]=found
                if cache.structural[x['function']]:args[i]=exposed
        if f['recursive'] is not None and 'Construct' not in args[f['recursive']]:return call(x['function'],args)
        # Small authoring jobs should not pay for structural keys. Repeated
        # expansion earns the bounded cache within this invocation only.
        cache.calls+=1;key=None
        if cache.calls>cache.WARMUP_CALLS:
            key=cache.key(x['function'],args,depth);cached=cache.get(key)
            if cached is not None:return json.loads(cached)
        body=f['body']
        def selfcalls(x):
            if isinstance(x,dict):
                if 'SelfCall' in x:return call(t['Call']['function'],[selfcalls(a) for a in x['SelfCall']])
                return {k:selfcalls(v) for k,v in x.items()}
            if isinstance(x,list):return [selfcalls(v) for v in x]
            return x
        result=recur(sub(selfcalls(body),dict(zip([n for n,_ in f['params']],args))))
        if key is not None:cache.put(key,result)
        return result
    if 'If' in t:
        x=t['If'];c=recur(x['condition'])
        if 'Bool' in c:return recur(x['on_true' if c['Bool'] else 'on_false'])
        return choice(c,recur(x['on_true']),recur(x['on_false']))
    if 'Construct' in t:
        x=t['Construct'];return cons(x['datatype'],x['constructor'],[recur(a) for a in x['arguments']])
    if 'Match' in t:
        x=t['Match'];scrutinee=_constructor_head(recur(x['scrutinee']),objects,heads,depth+1)
        if 'Construct' in scrutinee:
            c=scrutinee['Construct'];b=x['branches'][c['constructor']];return recur(sub(b['body'],dict(zip(b['bindings'],c['arguments']))))
        branches=[]
        for b in x['branches']:
            bindings=list(b['bindings']);used=free_variables(b['body']);occupied=variables(b['body'])|binding_names(b['body'])
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
        # Closed binary32 proposals use exact integer rounding. They remain
        # ordinary conversions that the independent kernel must replay.
        if 'U64' in a and 'U64' in z and x['op'].startswith('f32:'):
            proposed = fixed_f32(x['op'],a['U64'],z['U64'])
            if proposed is not None:return proposed
        if 'U64' in a and 'U64' in z and x['op'] in ['==','!=','<','<=','>','>=','+','-','*','&']:
            av,zv=a['U64'],z['U64'];op=x['op'];return {'Bool':{'==':av==zv,'!=':av!=zv,'<':av<zv,'<=':av<=zv,'>':av>zv,'>=':av>=zv}[op]} if op in ['==','!=','<','<=','>','>='] else {'U64':{'+':av+zv,'-':av-zv,'*':av*zv,'&':av&zv}[op]%(1<<64)}
        if 'Bool'in a and 'Bool'in z:
            av,zv=a['Bool'],z['Bool'];op=x['op']
            return {'Bool':{'&&':av and zv,'||':av or zv,'==':av==zv,'!=':av!=zv}[op]}
        return binary(x['op'],a,z)
    return t

def lift(eq,context,variable='delta_hole'):return {'Substitute':dict(variable=variable,context=context,equality=eq)}
def equality(a,z,objects,hyp=None,facts=(),rewrite=replace):
    facts=tuple((normal(left,objects),normal(right,objects),index) for left,right,index in facts)
    def simplify(t):
        current=normal(t,objects);proof=convert(t,current)
        for _ in range(16):
            changed=False
            for left,right,index in facts:
                rewritten=rewrite(current,left,right)
                if rewritten!=current:
                    context=rewrite(current,left,var('delta_hole'))
                    following=normal(rewritten,objects)
                    proof=trans(proof,lift(index if isinstance(index,dict) else {'Hypothesis':index},context),convert(rewritten,following))
                    current=following;changed=True
            if not changed:return current,proof
        raise ValueError('point delta tactic rewrite budget')
    na,pa=simplify(a);nz,pz=simplify(z)
    from producers.action_replacement import alpha_normal
    if alpha_normal(na)==alpha_normal(nz):return trans(pa,convert(na,nz),{'Sym':pz})
    if hyp:
        ha,hz,index=hyp;ha,ha_proof=simplify(ha);hz,hz_proof=simplify(hz)
        inherited=trans({'Sym':ha_proof},index if isinstance(index,dict) else {'Hypothesis':index},hz_proof)
        context=replace(na,ha,var('delta_hole'));rewritten=replace(na,ha,hz)
        if normal(rewritten,objects)==nz:return trans(pa,lift(inherited,context),convert(rewritten,nz),{'Sym':pz})
    raise ValueError('point delta proof tactic cannot establish this equation: '+str((na,nz)))

def legacy_setup(model,cache,add,objects):
    reply=cache['case']['normal']['Construct']['arguments'][0]
    if 'Match' in reply:
        from producers.point_delta_mapped import setup as mapped_setup
        return mapped_setup(model,cache,add,objects,False)
    if 'Call' not in reply:raise ValueError('--delta-query needs a fixed-key get or mapped get query')
    f=reply['Call'];tables=[t for t in model['tables'] if t['get']==f['function']]
    if len(tables)!=1 or len(f['arguments'])!=2 or 'U64' not in f['arguments'][1]:raise ValueError('--delta-query needs a fixed-u64-key table get')
    table=tables[0];root=f['arguments'][0];q=f['arguments'][1]
    if 'Var' not in root or root['Var'] not in cache['case']['bindings']:raise ValueError('unsupported point-query root')
    index=cache['case']['bindings'].index(root['Var']);d=table['datatype'];get=table['get'];option=objects[get]['payload']['declaration']['Function']['result']['Data']
    none=cons(option,0,[]);some=lambda x:cons(option,1,[x]);getof=lambda r:call(get,[r,q]);params=[['rows',{'Data':d}]]
    rows=var('rows');tail=var('delta_tail');head=var('delta_key');value=var('delta_value');new=var('delta_new')
    bound=cons(d,1,[head,value,tail]);guard=binary('==',q,head)
    updates={}
    for name in ['remove','replace']:
        change=lambda r:call(table[name],[r,q]+([new] if name=='replace' else []))
        result=lambda r:none if name=='remove' else match(getof(r),[([],none),(['delta_old'],some(new))])
        lhs=lambda r:getof(change(r));rhs=result
        a,z=lhs(bound),rhs(bound);na,nz=normal(a,objects),normal(z,objects);branches={}
        for flag in [False,True]:
            context_a=replace(na,guard,var('delta_hole'));context_z=replace(nz,guard,var('delta_hole'))
            ca=replace(na,guard,{'Bool':flag});cz=replace(nz,guard,{'Bool':flag})
            branches['on_true' if flag else 'on_false']=trans(convert(a,na),lift({'Hypothesis':1},context_a),equality(ca,cz,objects,(lhs(tail),rhs(tail),0),[(guard,{'Bool':flag},1)]),{'Sym':lift({'Hypothesis':1},context_z)},convert(nz,z))
        proof={'Induction':dict(variable='rows',**{'from':lhs(rows),'to':rhs(rows)},cases=[dict(bindings=[],proof=convert(lhs(cons(d,0,[])),rhs(cons(d,0,[])))),dict(bindings=['delta_key','delta_value','delta_tail'],proof={'BoolSplit':dict(condition=guard,**{'from':a,'to':z},**branches)})])}
        decl={'Theorem':dict(params=params+([['delta_new',objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]]] if name=='replace' else []),conditions=[],**{'from':lhs(rows),'to':rhs(rows)},proof=proof)}
        updates[name]=add(decl,[d,option])
    def recipe(t,old,bindings):
        if t==var(bindings[index]):return old
        c=t.get('Call',{});args=c.get('arguments',[])
        if len(args)<2 or args[1]!=q:raise ValueError('unsupported update key')
        if c['function']==table['remove']:
            recipe(args[0],old,bindings);return none
        if c['function']==table['replace']:
            prior=recipe(args[0],old,bindings);return match(prior,[([],none),(['delta_old'],some(args[2]))])
        raise ValueError('unsupported point delta operation')
    def action(sa):
        old=var('cached_reply')
        initial=var(sa['case']['bindings'][index])
        def predict(term):
            if 'If' in term:
                branch=term['If'];yes=predict(branch['on_true']);no=predict(branch['on_false'])
                if yes==no:return yes
                condition=replace(branch['condition'],getof(initial),old)
                return choice(condition,yes,no)
            o=term['Construct']
            if o['constructor']!=0 or o['arguments'][1]!={'Bool':True}:return old
            return recipe(o['arguments'][3]['Construct']['arguments'][index],old,sa['case']['bindings'])
        try:predicted=predict(sa['case']['normal'])
        except (ValueError,KeyError):return None
        if free_variables(predicted)-{'cached_reply',*[n for n,_ in sa['params'][1:]]}:return None
        return predicted
    def query_equality(root,bindings):
        """get(updated roots) = candidate cache; exact universal update laws."""
        if root==var(bindings[index]):return {'Refl':getof(root)}
        c=root['Call'];args=c['arguments'];name='remove' if c['function']==table['remove'] else 'replace'
        use={'Use':dict(theorem=updates[name],arguments=[args[0]]+([args[2]] if name=='replace' else []),premises=[])}
        if name=='remove':return use
        context=match(var('delta_hole'),[([],none),(['delta_old'],some(args[2]))])
        return trans(use,lift(query_equality(args[0],bindings),context))
    return dict(action=action,recipe=recipe,equality=query_equality,index=index,get=get,q=q,option=option,updates=updates,table=table,some=some)

def setup(model,cache,add,objects):
    from producers.point_projection_delta import setup as projected_setup
    reply=cache['case']['normal']['Construct']['arguments'][0]
    if 'Match' in reply:
        try:return legacy_setup(model,cache,add,objects)
        except ValueError:pass
    return projected_setup(model,cache,add,objects)
