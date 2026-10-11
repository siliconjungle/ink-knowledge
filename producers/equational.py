"""Bounded, untrusted equality authoring from ordinary imported equations.

No tactic result is authority. Convert, Use, Substitute and BoolSplit are
independently checked by the existing first-order kernel.
"""
from producers.action_replacement import var, call, convert, trans
from producers.point_delta import normal, sub, replace, lift


def factor(proof, params, conditions, add):
    """Share branch derivations as bounded ordinary conditional theorems."""
    if 'BoolSplit' in proof:
        x=proof['BoolSplit'];branches={}
        for key,flag in [('on_false',False),('on_true',True)]:
            branches[key]=factor(x[key],params,[*conditions,{'from':x['condition'],'to':{'Bool':flag}}],add)
        body={'BoolSplit':{**x,**branches}}
        ident=add({'Theorem':dict(params=params,conditions=conditions,**{k:x[k] for k in ['from','to']},proof=body)})
        return {'Use':dict(theorem=ident,arguments=[var(n) for n,_ in params],premises=[{'Hypothesis':i} for i in range(len(conditions))])}
    return proof


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
    def __init__(self, objects, rules=(), opaque=(), algebra=None):
        self.objects, self.rules, self.opaque = objects, list(rules), set(opaque)
        self.algebra=algebra

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
            if match(law['from'], t):
                premises=[]
                for condition in law['conditions']:
                    found=False
                    for a,z,index in hypotheses:
                        saved=dict(bindings)
                        if match(condition['from'],self.norm(a)) and match(condition['to'],self.norm(z)):
                            premises.append({'Hypothesis':index});found=True;break
                        bindings.clear();bindings.update(saved)
                    if not found:break
                else:
                    if params <= bindings.keys():
                        target=sub(law['to'],bindings)
                        if target!=t:return t,target,{'Use':dict(theorem=ident,arguments=[bindings[n] for n,_ in law['params']],premises=premises)}
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
                a,z = self.norm(a), self.norm(z)
                following = replace(current,a,z)
                if following != current:
                    proof = trans(proof, lift({'Hypothesis': index}, replace(current,a,var('delta_hole'))), convert(following,self.norm(following)))
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
                for v in t.values(): yield from conditions(v)
            elif isinstance(t,list):
                for v in t: yield from conditions(v)
        condition = next((c for c in conditions([na,nz]) if not any(conditions(c))),None)
        if condition is None:
            if self.algebra:return trans(pa,self.algebra(na,nz),{'Sym':pz})
            raise ValueError('equational tactic cannot close: '+str((na,nz))[:1600])
        index = len(hypotheses)+len(facts)
        branches = {name:self.prove(a,z,hypotheses,(*facts,(condition,{'Bool':flag},index)),depth+1)
                    for name,flag in [('on_false',False),('on_true',True)]}
        return {'BoolSplit':dict(condition=condition,**{'from':a,'to':z},**branches)}
