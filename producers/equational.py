"""Bounded, untrusted equality authoring from ordinary imported equations.

No tactic result is authority. Convert, Use, Substitute and BoolSplit are
independently checked by the existing first-order kernel.
"""
from producers.action_replacement import var, call, cons, trans
from producers.action_replacement import convert as _convert
from producers.point_delta import normal, sub, replace, lift


def unshadow(t):
    """The same term with no binder shadowing a variable already in scope.

    `alpha` names binders by depth, so replacing a subterm under a binder with
    a separately normalised term can repeat a canonical name, which the kernel
    rejects. Renaming the inner binder apart is alpha-equivalent, and the
    kernel compares proof junctions modulo alpha.
    """
    used, free = set(), set()
    def collect(t, bound):
        if isinstance(t, list):
            for x in t: collect(x, bound)
        elif isinstance(t, dict):
            if set(t) == {'Var'}:
                used.add(t['Var'])
                if t['Var'] not in bound: free.add(t['Var'])
            elif 'Match' in t and isinstance(t['Match'], dict) and 'branches' in t['Match']:
                collect(t['Match']['scrutinee'], bound)
                for b in t['Match']['branches']:
                    if len(set(b['bindings'])) < len(b['bindings']) or bound & set(b['bindings']): clash.append(True)
                    binders.update(b['bindings']); used.update(b['bindings'])
                    collect(b['body'], bound | set(b['bindings']))
            else:
                for v in t.values(): collect(v, bound)
    clash, binders = [], set()
    collect(t, frozenset())
    if not clash and not binders & free: return t
    serial = [0]
    def fresh():
        while 'eq_apart_' + str(serial[0]) in used: serial[0] += 1
        name = 'eq_apart_' + str(serial[0]); used.add(name); return name
    def go(t, bound, env):
        if isinstance(t, list): return [go(x, bound, env) for x in t]
        if not isinstance(t, dict): return t
        if set(t) == {'Var'}: return var(env.get(t['Var'], t['Var']))
        if 'Match' in t and isinstance(t['Match'], dict) and 'branches' in t['Match']:
            x = t['Match']; branches = []
            for b in x['branches']:
                local, names = dict(env), []
                for n in b['bindings']:
                    m = fresh() if n in bound or n in names else n
                    local[n] = m; names.append(m)
                branches.append({**b, 'bindings': names, 'body': go(b['body'], bound | set(names), local)})
            return {'Match': {**x, 'scrutinee': go(x['scrutinee'], bound, env), 'branches': branches}}
        return {k: go(v, bound, env) for k, v in t.items()}
    return go(t, frozenset(free), {})


def convert(a, b): return _convert(unshadow(a), unshadow(b))


def factor(proof, params, conditions, add, objects=None):
    """Share branch derivations as bounded ordinary conditional theorems."""
    if 'BoolSplit' in proof:
        x=proof['BoolSplit'];branches={}
        for key,flag in [('on_false',False),('on_true',True)]:
            branches[key]=factor(x[key],params,[*conditions,{'from':x['condition'],'to':{'Bool':flag}}],add,objects)
        body={'BoolSplit':{**x,**branches}}
        ident=add({'Theorem':dict(params=params,conditions=conditions,**{k:x[k] for k in ['from','to']},proof=body)})
        return {'Use':dict(theorem=ident,arguments=[var(n) for n,_ in params],premises=[{'Hypothesis':i} for i in range(len(conditions))])}
    if objects is None:return proof
    def endpoints(p):
        if 'Convert' in p:return p['Convert']['from'],p['Convert']['to']
        if 'Refl' in p:return p['Refl'],p['Refl']
        if 'Hypothesis' in p:c=conditions[p['Hypothesis']];return c['from'],c['to']
        if 'Use' in p:
            x=p['Use'];d=objects[x['theorem']]['payload']['declaration']['Theorem'];env=dict(zip([n for n,_ in d['params']],x['arguments']));return sub(d['from'],env),sub(d['to'],env)
        if 'Sym' in p:a,z=endpoints(p['Sym']);return z,a
        if 'Trans' in p:return endpoints(p['Trans'][0])[0],endpoints(p['Trans'][1])[1]
        if 'Substitute' in p:
            x=p['Substitute'];a,z=endpoints(x['equality']);return sub(x['context'],{x['variable']:a}),sub(x['context'],{x['variable']:z})
        for k in ['Call','Construct']:
            if k in p:
                x=p[k];parts=[endpoints(q) for q in x['arguments']];return tuple({k:{**x,'arguments':[q[j] for q in parts]}} for j in [0,1])
        if 'Binary' in p:
            x=p['Binary'];a,z=endpoints(x['left']),endpoints(x['right']);return tuple({'Binary':dict(op=x['op'],left=a[i],right=z[i])} for i in [0,1])
        for k in ['BoolSplit','Induction','GeneralizedInduction','BoolCases','BitVector']:
            if k in p:return p[k]['from'],p[k]['to']
        raise ValueError('unknown factoring proof')
    if 'Trans' in proof:body={'Trans':[factor(p,params,conditions,add,objects) for p in proof['Trans']]}
    elif 'Sym' in proof:body={'Sym':factor(proof['Sym'],params,conditions,add,objects)}
    elif 'Substitute' in proof:body={'Substitute':{**proof['Substitute'],'equality':factor(proof['Substitute']['equality'],params,conditions,add,objects)}}
    elif 'Use' in proof:body={'Use':{**proof['Use'],'premises':[factor(p,params,conditions,add,objects) for p in proof['Use']['premises']]}}
    elif 'Binary' in proof:body={'Binary':{**proof['Binary'],**{k:factor(proof['Binary'][k],params,conditions,add,objects) for k in ['left','right']}}}
    else:
        body=proof
        for k in ['Call','Construct']:
            if k in proof:body={k:{**proof[k],'arguments':[factor(p,params,conditions,add,objects) for p in proof[k]['arguments']]}}
    def depth(p):
        if isinstance(p,dict):return 1+max([depth(v) for v in p.values()]+[0])
        if isinstance(p,list):return 1+max([depth(v) for v in p]+[0])
        return 0
    if body!=proof or 'Trans' in proof or 'Use' in proof or 'Substitute' in proof:
        if depth(body)>32:
            a,z=endpoints(body);ident=add({'Theorem':dict(params=params,conditions=conditions,**{'from':a,'to':z},proof=body)})
            return {'Use':dict(theorem=ident,arguments=[var(n) for n,_ in params],premises=[{'Hypothesis':i} for i in range(len(conditions))])}
    return body


def alpha(t, env=None, depth=0):
    env = env or {}
    if isinstance(t, list): return [alpha(x, env, depth) for x in t]
    if not isinstance(t, dict): return t
    if set(t) == {'Var'}: return var(env.get(t['Var'], t['Var']))
    if 'Match' in t:
        x = t['Match']; branches = []
        for b in x['branches']:
            names = ['eq_bound_' + str(depth) + '_' + str(i) for i in range(len(b['bindings']))]
            branches.append(dict(bindings=names, body=alpha(b['body'], {**env, **dict(zip(b['bindings'], names))}, depth+1)))
        return {'Match': dict(scrutinee=alpha(x['scrutinee'], env, depth), branches=branches)}
    return {k: alpha(v, env, depth) for k, v in t.items()}


class Tactic:
    def __init__(self, objects, rules=(), opaque=(), algebra=None, prove_conditions=False, add=None, params=()):
        self.objects, self.rules, self.opaque = objects, list(rules), set(opaque)
        self.algebra=algebra
        self.prove_conditions=prove_conditions; self.condition_stack=[]
        self.add=add;self.params=dict(params);self.case_serial=0
        self.patterns={}

    def norm(self, t): return alpha(normal(t, self.objects, opaque=self.opaque))

    def rewrite(self, t, hypotheses=()):
        for ident in self.rules:
            law = self.objects[ident]['payload']['declaration']['Theorem']
            params = {n for n, _ in law['params']}; bindings = {}
            def match(pattern, value):
                if isinstance(pattern, dict) and set(pattern) == {'Var'} and pattern['Var'] in params:
                    n = pattern['Var']
                    if n in bindings: return bindings[n] == value
                    bindings[n] = value; return True
                if type(pattern) is not type(value): return False
                if isinstance(pattern, dict): return pattern.keys() == value.keys() and all(match(pattern[k], value[k]) for k in pattern)
                if isinstance(pattern, list): return len(pattern) == len(value) and all(match(a,b) for a,b in zip(pattern,value))
                return pattern == value
            if ident not in self.patterns:self.patterns[ident]=(self.norm(law['from']),[(self.norm(c['from']),self.norm(c['to'])) for c in law['conditions']])
            pattern,condition_patterns=self.patterns[ident]
            if match(pattern, t):
                premises=[]
                for condition,(cf,ct) in zip(law['conditions'],condition_patterns):
                    found=False
                    for a,z,index in hypotheses:
                        saved=dict(bindings)
                        if match(cf,self.norm(a)) and match(ct,self.norm(z)):
                            premises.append({'Hypothesis':index});found=True;break
                        bindings.clear();bindings.update(saved)
                    if not found and self.prove_conditions and params <= bindings.keys():
                        a,z=sub(condition['from'],bindings),sub(condition['to'],bindings)
                        marker=(str(self.norm(a)),str(self.norm(z)))
                        if marker not in self.condition_stack and len(self.condition_stack)<8:
                            self.condition_stack.append(marker)
                            try:
                                unique={i:(x,y,i) for x,y,i in hypotheses}
                                premises.append(self.prove(a,z,hypotheses=[unique[i] for i in sorted(unique)]));found=True
                            except ValueError:pass
                            finally:self.condition_stack.pop()
                    if not found:break
                else:
                    if params <= bindings.keys():
                        target=sub(law['to'],bindings)
                        if target!=t:return t,target,trans(convert(t,sub(law['from'],bindings)),{'Use':dict(theorem=ident,arguments=[bindings[n] for n,_ in law['params']],premises=premises)})
        # Never lift a branch-local proof outside its binder scope.
        if isinstance(t, dict):
            children = [t['Match']['scrutinee']] if 'Match' in t else list(t.values())
        elif isinstance(t, list): children = t
        else: children = []
        for child in children:
            found = self.rewrite(child,hypotheses)
            if found: return found
        return None

    def simplify(self, t, hypotheses):
        current = self.norm(t); proof = convert(t, current)
        for _ in range(96):
            changed = False
            for a,z,index in hypotheses:
                original_a,original_z=a,z;a,z = self.norm(a), self.norm(z)
                left_proof,right_proof=convert(original_a,a),convert(original_z,z);specialized=False
                # A Boolean case can specialize an induction parameter itself.
                # Keep the hypothesis usable after that substitution, and prove
                # the specialization by congruence from the exact branch facts.
                for x,y,j in hypotheses:
                    if j==index or 'Bool' not in y:continue
                    x=self.norm(x)
                    for side in [0,1]:
                        value=a if side==0 else z;updated=replace(value,x,y)
                        if updated==value:continue
                        specialized=True
                        p=trans(lift({'Hypothesis':j},replace(value,x,var('delta_hole'))),convert(updated,self.norm(updated)))
                        if side==0:left_proof=trans(left_proof,p);a=self.norm(updated)
                        else:right_proof=trans(right_proof,p);z=self.norm(updated)
                equality=trans({'Sym':left_proof},{'Hypothesis':index},right_proof) if specialized else {'Hypothesis':index}
                following = replace(current,a,z)
                if following != current:
                    proof = trans(proof, lift(equality, replace(current,a,var('delta_hole'))), convert(following,self.norm(following)))
                    current = self.norm(following); changed = True; break
            if changed: continue
            found = self.rewrite(current,hypotheses)
            if found:
                a,z,p = found; following = replace(current,a,z)
                proof = trans(proof,lift(p,replace(current,a,var('delta_hole'))),convert(following,self.norm(following)))
                current = self.norm(following); continue
            return current, proof
        raise ValueError('equational tactic rewrite budget')

    def prove(self, a, z, hypotheses=(), facts=(), depth=0):
        if depth > 12: raise ValueError('equational tactic split budget')
        na,pa = self.simplify(a,[*facts,*hypotheses,*facts])
        nz,pz = self.simplify(z,[*facts,*hypotheses,*facts])
        if na == nz: return trans(pa,convert(na,nz),{'Sym':pz})
        def conditions(t):
            if isinstance(t,dict):
                if 'If' in t: yield t['If']['condition']
                if 'Match' in t:
                    yield from conditions(t['Match']['scrutinee']);return
                for v in t.values(): yield from conditions(v)
            elif isinstance(t,list):
                for v in t: yield from conditions(v)
        condition = next((c for c in conditions([na,nz]) if not any(conditions(c))),None)
        if condition is None:
            if self.add and depth<12:
                def matches(t):
                    if isinstance(t,dict):
                        if 'Match' in t:
                            yield t['Match']['scrutinee'];yield from matches(t['Match']['scrutinee']);return
                        for v in t.values():yield from matches(v)
                    elif isinstance(t,list):
                        for v in t:yield from matches(v)
                def sort(t,env):
                    if 'Var' in t:return env[t['Var']]
                    if 'Construct' in t:return {'Data':t['Construct']['datatype']}
                    if 'Call' in t:return self.objects[t['Call']['function']]['payload']['declaration']['Function']['result']
                    if 'If' in t:return sort(t['If']['on_true'],env)
                    if 'Bool' in t:return 'Bool'
                    if 'U64' in t:return 'U64'
                    if 'Match' in t:
                        x=t['Match'];s=sort(x['scrutinee'],env);decl=self.objects[s['Data']]['payload']['declaration']['Datatype']['constructors'][0];b=x['branches'][0]
                        return sort(b['body'],{**env,**dict(zip(b['bindings'],[s if f=='SelfType' else f for f in decl['fields']]))})
                    raise ValueError('unknown authoring term sort')
                def occurs(value,t):
                    if value==t:return True
                    if isinstance(t,dict):return any(occurs(value,v) for v in t.values())
                    if isinstance(t,list):return any(occurs(value,v) for v in t)
                    return False
                scrutinee=next((s for s in reversed(list(matches(na))) if occurs(s,nz)),None)
                if scrutinee is not None:
                    s=sort(scrutinee,self.params);data=s['Data'];serial=self.case_serial;self.case_serial+=1;name='equational_case_'+str(serial)
                    left,right=replace(na,scrutinee,var(name)),replace(nz,scrutinee,var(name));unique={i:(x,y,i) for x,y,i in [*hypotheses,*facts]};ordered=[unique[i] for i in sorted(unique)]
                    local_hyp=[(x,y,j) for j,(x,y,_) in enumerate(ordered)];cases=[];saved=dict(self.params)
                    for i,c in enumerate(self.objects[data]['payload']['declaration']['Datatype']['constructors']):
                        ns=[name+'_field_'+str(j) for j in range(len(c['fields']))];self.params={**saved,**dict(zip(ns,[s if f=='SelfType' else f for f in c['fields']]))}
                        value=cons(data,i,[var(n) for n in ns]);p=self.prove(sub(left,{name:value}),sub(right,{name:value}),local_hyp,depth=depth+1)
                        p=factor(p,list(self.params.items()),[dict(zip(['from','to'],[x,y])) for x,y,_ in ordered],self.add,self.objects)
                        cases.append(dict(bindings=ns,proof=p))
                    self.params=saved;params=[*saved.items(),[name,s]]
                    ident=self.add({'Theorem':dict(params=params,conditions=[dict(zip(['from','to'],[x,y])) for x,y,_ in ordered],**{'from':left,'to':right},proof={'Induction':dict(variable=name,**{'from':left,'to':right},cases=cases)})})
                    return trans(pa,{'Use':dict(theorem=ident,arguments=[*[var(n) for n in saved],scrutinee],premises=[{'Hypothesis':i} for _,_,i in ordered])},{'Sym':pz})
            if self.algebra:return trans(pa,self.algebra(na,nz),{'Sym':pz})
            raise ValueError('equational tactic cannot close: '+str((na,nz))[:1600])
        index = len(hypotheses)+len(facts)
        branches = {name:self.prove(a,z,hypotheses,(*facts,(condition,{'Bool':flag},index)),depth+1)
                    for name,flag in [('on_false',False),('on_true',True)]}
        return {'BoolSplit':dict(condition=condition,**{'from':a,'to':z},**branches)}
