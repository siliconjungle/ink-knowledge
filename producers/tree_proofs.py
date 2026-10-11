"""Bounded, untrusted equality authoring for generic constructor definitions.

Only Convert, congruence, exhaustive Cases/BoolSplit, checked lemma use and
explicit induction hypotheses are emitted. No tree algorithm is kernel authority.
"""
from action_replacement import var, call, cons, convert, trans
from point_delta import normal, replace, sub
import json


class Tactic:
    def __init__(self, objects, add):
        self.objects, self.add = objects, add
        self.rules, self.serial, self.work, self.blocked = [], 0, 0, set()
        self.cases_first=True
        self.scalar=None
        self.eager=set()
        self.transparent=set()
        self.arithmetic=None

    def normal(self,t,env):
        t=normal(t,self.objects,blocked=self.blocked,eager=self.eager)
        avoid=set(env);counter=[0]
        def rename(t,bindings):
            if isinstance(t,list):return [rename(x,bindings)for x in t]
            if not isinstance(t,dict):return t
            if set(t)=={'Var'}:return var(bindings.get(t['Var'],t['Var']))
            if 'Match'in t:
                x=t['Match'];branches=[]
                for b in x['branches']:
                    ns=[]
                    for old in b['bindings']:
                        n='tree_bound_'+str(counter[0]);counter[0]+=1
                        while n in avoid:n='tree_bound_'+str(counter[0]);counter[0]+=1
                        ns.append(n)
                    branches.append(dict(bindings=ns,body=rename(b['body'],{**bindings,**dict(zip(b['bindings'],ns))})))
                return {'Match':dict(scrutinee=rename(x['scrutinee'],bindings),branches=branches)}
            return {k:rename(v,bindings)for k,v in t.items()}
        return rename(t,{})

    def sort(self, t, env):
        kind,x=next(iter(t.items()))
        if kind=='Var':return env[x]
        if kind in ('Bool','U64'):return kind
        if kind=='Construct':return {'Data':x['datatype']}
        if kind=='Call':return self.objects[x['function']]['payload']['declaration']['Function']['result']
        if kind=='If':return self.sort(x['on_true'],env)
        if kind=='Binary':return 'Bool' if x['op'] in ('==','!=','<','<=','>','>=','&&','||') else 'U64'
        if kind=='Match':
            d=self.sort(x['scrutinee'],env)['Data'];cs=self.objects[d]['payload']['declaration']['Datatype']['constructors'];b=x['branches'][0]
            local={**env,**{n:({'Data':d} if s=='SelfType' else s)for n,s in zip(b['bindings'],cs[0]['fields'])}}
            return self.sort(b['body'],local)
        raise ValueError('cannot infer tactic term '+kind)

    def register(self, identity):
        t=self.objects[identity]['payload']['declaration']['Theorem']
        self.rules.append((t['from'],t['to'],[n for n,_ in t['params']],t['conditions'],lambda xs,ps,i=identity:{'Use':dict(theorem=i,arguments=xs,premises=ps)}))
        def preserve(term):
            if isinstance(term,dict):
                if 'Call'in term:
                    x=term['Call'];f=self.objects[x['function']]['payload']['declaration']['Function']
                    if f['recursive'] is None and x['function'] not in self.transparent:self.blocked.add(x['function'])
                for child in term.values():preserve(child)
            elif isinstance(term,list):
                for child in term:preserve(child)
        preserve(t['from'])

    def unify(self, pattern, term, variables, bound=None):
        bound={} if bound is None else bound
        if isinstance(pattern,dict) and set(pattern)=={'Var'} and pattern['Var'] in variables:
            n=pattern['Var']
            if n in bound and bound[n]!=term:return None
            return {**bound,n:term}
        if type(pattern)!=type(term):return None
        if isinstance(pattern,dict):
            if pattern.keys()!=term.keys():return None
            for k,v in pattern.items():
                bound=self.unify(v,term[k],variables,bound)
                if bound is None:return None
            return bound
        if isinstance(pattern,list):
            if len(pattern)!=len(term):return None
            for a,b in zip(pattern,term):
                bound=self.unify(a,b,variables,bound)
                if bound is None:return None
            return bound
        return bound if pattern==term else None

    def rewrite(self, term, rules, facts):
        for a,z,names,conditions,use in rules:
            bindings=self.unify(a,term,set(names))
            if bindings is None or any(n not in bindings for n in names):continue
            premises=[]
            for condition in conditions:
                wanted=sub(condition,bindings)
                found=next((p for l,r,p in facts if normal(l,self.objects)==normal(wanted['from'],self.objects) and normal(r,self.objects)==normal(wanted['to'],self.objects)),None)
                if found is None:break
                premises.append(found)
            else:
                updated=sub(z,bindings)
                if updated!=term:return updated,use([bindings[n]for n in names],premises)
        children=[]
        if isinstance(term,dict):
            for k,v in term.items():
                if isinstance(v,(list,dict)):children.append((k,v))
        elif isinstance(term,list):children=list(enumerate(term))
        for key,child in children:
            result=self.rewrite(child,rules,facts)
            if result:
                changed,proof=result
                output=dict(term) if isinstance(term,dict) else list(term);output[key]=changed
                # Congruence is always lifted through a typed complete term by
                # the caller; these intermediate JSON records are not terms.
                return output,proof
        return None

    def simplify(self, term, env, rules, facts, hypotheses, depth):
        hole='tree_proof_hole'
        while hole in env:hole+='_' 
        original_facts=facts
        structural=list(facts)
        prepared=[]
        for index,(a,z,p) in enumerate(facts):
            original_a=a
            for _ in range(4):
                a,z=self.normal(a,env),self.normal(z,env)
                changed=False
                for c,d,q in structural:
                    if c==original_a:continue
                    aa,zz=replace(a,c,d),replace(z,c,d)
                    if aa!=a:
                        cp={'Substitute':dict(variable=hole,context=replace(a,c,var(hole)),equality=q)}
                        p=trans({'Sym':cp},p);a=aa;changed=True
                    if zz!=z:
                        cp={'Substitute':dict(variable=hole,context=replace(z,c,var(hole)),equality=q)}
                        p=trans(p,cp);z=zz;changed=True
                if not changed:break
            if hypotheses==len(original_facts) and len(env)<=64 and len(json.dumps(p,separators=(',',':')))>500:
                params=sorted(env.items());conditions=[dict(**{'from':l,'to':r})for l,r,_ in original_facts]
                key=self.add({'Theorem':dict(params=params,conditions=conditions,**{'from':a,'to':z},proof=p)})
                p={'Use':dict(theorem=key,arguments=[var(n)for n,_ in params],premises=[p for _,_,p in original_facts])}
            prepared.append((a,z,p))
        facts=[*original_facts,*prepared]
        current=self.normal(term,env)
        proof=convert(term,current)if current!=term else None
        def factor():
            nonlocal proof
            def schema(t):
                if isinstance(t,dict):return 'GeneralizedHypothesis'in t or any(schema(v)for v in t.values())
                if isinstance(t,list):return any(schema(v)for v in t)
                return False
            if proof is not None and hypotheses==len(original_facts) and len(env)<=64 and len(json.dumps(proof,separators=(',',':')))>500 and not schema(proof):
                params=sorted(env.items());conditions=[dict(**{'from':l,'to':r})for l,r,_ in original_facts]
                key=self.add({'Theorem':dict(params=params,conditions=conditions,**{'from':term,'to':current},proof=proof)})
                proof={'Use':dict(theorem=key,arguments=[var(n)for n,_ in params],premises=[p for _,_,p in original_facts])}
        def append(p,target):
            nonlocal proof,current
            proof=p if proof is None else trans(proof,p)
            current=target
            factor()
        factor()
        for _ in range(80):
            changed=False
            for a,z,p in facts:
                updated=replace(current,a,z)
                if updated!=current:
                    context=replace(current,a,var(hole))
                    append({'Substitute':dict(variable=hole,context=context,equality=p)},updated)
                    current=updated;changed=True
            # Search on complete subterms; lift the exact replacement through
            # the enclosing term rather than assuming an unchecked rewrite.
            def find(t):
                if not isinstance(t,(dict,list)):return None
                if isinstance(t,dict) and len(t)==1 and next(iter(t)) in ('Var','Call','Construct','If','Match','Binary','U64','Bool'):
                    for a,z,names,conditions,use in rules:
                        binding=self.unify(a,t,set(names))
                        if binding is None or any(n not in binding for n in names):continue
                        premises=[]
                        for condition in conditions:
                            wanted=sub(condition,binding)
                            found=next((p for l,r,p in facts if normal(l,self.objects)==normal(wanted['from'],self.objects) and normal(r,self.objects)==normal(wanted['to'],self.objects)),None)
                            if found is None and self.scalar is not None:
                                try:found=self.scalar.prove(wanted['from'],wanted['to'],env,facts)
                                except ValueError:pass
                            if found is None and self.scalar is not None and depth<12:
                                # Nested conditional laws may prove their own
                                # premises (for example a composed constructor).
                                try:found=self.equality(wanted['from'],wanted['to'],env,rules,original_facts,hypotheses,depth+1)
                                except ValueError:pass
                            if found is None:break
                            premises.append(found)
                        else:
                            target=sub(z,binding)
                            if target!=t:return t,target,use([binding[n]for n in names],premises)
                for child in (t.values() if isinstance(t,dict) else t):
                    found=find(child)
                    if found:return found
                return None
            found=find(current)
            if found:
                a,z,p=found;context=replace(current,a,var(hole));updated=replace(current,a,z)
                append({'Substitute':dict(variable=hole,context=context,equality=p)},updated)
                current=updated;changed=True
            normalized=self.normal(current,env)
            if normalized!=current:
                append(convert(current,normalized),normalized);changed=True
            if not changed:return current,proof if proof is not None else {'Refl':term},facts
        raise ValueError('tree tactic rewrite budget')

    def equality(self,a,z,env,rules=None,facts=(),hypotheses=0,depth=0):
        self.work+=1
        if self.work>20000 or depth>16:raise ValueError('tree tactic case/work bound '+str([(l,r)for l,r,_ in facts])[-2400:])
        rules=self.rules if rules is None else rules
        na,pa,prepared=self.simplify(a,env,rules,facts,hypotheses,depth);nz,pz,_=self.simplify(z,env,rules,facts,hypotheses,depth)
        def emit(p):
            def schema(t):
                if isinstance(t,dict):return 'GeneralizedHypothesis'in t or any(schema(v)for v in t.values())
                if isinstance(t,list):return any(schema(v)for v in t)
                return False
            if hypotheses==len(facts) and len(env)<=64 and not schema(p) and len(json.dumps(p,separators=(',',':')))>500:
                params=sorted(env.items());conditions=[dict(**{'from':l,'to':r})for l,r,_ in facts]
                identity=self.add({'Theorem':dict(params=params,conditions=conditions,**{'from':a,'to':z},proof=p)})
                return {'Use':dict(theorem=identity,arguments=[var(n)for n,_ in params],premises=[p for _,_,p in facts])}
            return p
        finish=lambda p:emit(trans(pa,p,{'Sym':pz}))
        if na==nz:return finish(convert(na,nz))
        if 'Construct' in na and 'Construct' in nz:
            x,y=na['Construct'],nz['Construct']
            if (x['datatype'],x['constructor'])==(y['datatype'],y['constructor']):
                return finish({'Construct':dict(datatype=x['datatype'],constructor=x['constructor'],arguments=[self.equality(l,r,env,rules,facts,hypotheses,depth+1)for l,r in zip(x['arguments'],y['arguments'])])})
        def candidates(t,kind):
            if isinstance(t,dict):
                if kind in t:yield t[kind]['condition' if kind=='If' else 'scrutinee']
                for child in t.values():yield from candidates(child,kind)
            elif isinstance(t,list):
                for child in t:yield from candidates(child,kind)
        if self.arithmetic is not None and self.sort(na,env)=='U64':
            try:return finish(self.arithmetic(na,nz))
            except ValueError:pass
        if self.scalar is not None and self.sort(na,env)in ('Bool','U64'):
            try:return finish(self.scalar.prove(na,nz,env,prepared))
            except ValueError:pass
        condition=next((t for t in candidates([na,nz],'If')if 'Bool'not in t),None)
        scrutinees=[t for t in candidates([na,nz],'Match')if 'Construct'not in t]
        scrutinee=next((t for t in scrutinees if 'Var'in t and t['Var'] in env),scrutinees[0]if scrutinees else None)
        def free(t):
            if isinstance(t,list):return set().union(*(free(x)for x in t))if t else set()
            if not isinstance(t,dict):return set()
            if set(t)=={'Var'}:return {t['Var']}
            if 'Match'in t:
                x=t['Match'];return free(x['scrutinee'])|set().union(*(free(b['body'])-set(b['bindings'])for b in x['branches']))
            return set().union(*(free(x)for x in t.values()))if t else set()
        if condition is not None and free(condition)<=set(env) and (not self.cases_first or scrutinee is None or 'Var'not in scrutinee):
            branches={}
            for flag in (False,True):
                branches['on_true' if flag else 'on_false']=self.equality(a,z,env,rules,(*facts,(condition,{'Bool':flag},{'Hypothesis':hypotheses})),hypotheses+1,depth+1)
            return emit({'BoolSplit':dict(condition=condition,**{'from':a,'to':z},**branches)})
        if scrutinee is not None:
            datatype=self.sort(scrutinee,env)['Data'];cs=self.objects[datatype]['payload']['declaration']['Datatype']['constructors'];cases=[]
            for i,c in enumerate(cs):
                self.serial+=1;bindings=['tree_case_'+str(self.serial)+'_'+str(j)for j in range(len(c['fields']))]
                local={**env,**{n:({'Data':datatype} if s=='SelfType' else s)for n,s in zip(bindings,c['fields'])}}
                constructed=cons(datatype,i,[var(n)for n in bindings])
                proof=self.equality(a,z,local,rules,(*facts,(scrutinee,constructed,{'Hypothesis':hypotheses})),hypotheses+1,depth+1)
                cases.append(dict(bindings=bindings,proof=proof))
            return emit({'Cases':dict(scrutinee=scrutinee,**{'from':a,'to':z},cases=cases)})
        if self.scalar is not None:
            try:
                contradiction=self.scalar.prove({'Bool':False},{'Bool':True},env,prepared)
                hole='tree_false_hole'
                while hole in env:hole+='_' 
                context={'If':dict(condition=var(hole),on_true=na,on_false=nz)}
                return finish({'Sym':{'Substitute':dict(variable=hole,context=context,equality=contradiction)}})
            except ValueError:pass
        raise ValueError(str(getattr(self.scalar,'last_error',''))+' tree equality residual '+str([na,nz])[:1200]+' facts '+str([(l,r)for l,r,_ in facts]))

    def theorem(self, name, params, a, z, induction=None, generalize=(), guard=None):
        bare_a,bare_z=a,z
        if guard is not None:a={'If':dict(condition=guard,on_true=a,on_false=z)}
        env=dict(params);self.work=0
        hole='tree_guard_hole'
        while hole in env:hole+='_' 
        if induction:
            datatype=env[induction]['Data'];cs=self.objects[datatype]['payload']['declaration']['Datatype']['constructors'];cases=[]
            for i,c in enumerate(cs):
                self.serial+=1;bindings=['tree_induct_'+str(self.serial)+'_'+str(j)for j in range(len(c['fields']))]
                local={**env,**{n:({'Data':datatype}if s=='SelfType'else s)for n,s in zip(bindings,c['fields'])}}
                local.pop(induction);bound=cons(datatype,i,[var(n)for n in bindings]);rules=list(self.rules);hypotheses=0;schema=0
                for n,s in zip(bindings,c['fields']):
                    if s!='SelfType':continue
                    ia,iz=sub(a,{induction:var(n)}),sub(z,{induction:var(n)})
                    if generalize:
                        index=schema;schema+=1
                        use=lambda xs,ps,index=index:{'GeneralizedHypothesis':dict(index=index,arguments=xs)}
                        rules.append((ia,iz,list(generalize),[],use))
                        if guard is not None:
                            ig=sub(guard,{induction:var(n)});ba=sub(bare_a,{induction:var(n)});bz=sub(bare_z,{induction:var(n)})
                            context={'If':dict(condition=var(hole),on_true=ba,on_false=bz)}
                            def conditional(xs,ps,index=index,context=context):
                                cx=sub(context,dict(zip(generalize,xs)))
                                return trans({'Sym':{'Substitute':dict(variable=hole,context=cx,equality=ps[0])}},{'GeneralizedHypothesis':dict(index=index,arguments=xs)})
                            rules.append((ba,bz,list(generalize),[dict(**{'from':ig,'to':{'Bool':True}})],conditional))
                    else:
                        p={'Hypothesis':hypotheses};hypotheses+=1
                        rules.append((ia,iz,[],[],lambda xs,ps,p=p:p))
                        if guard is not None:
                            ig=sub(guard,{induction:var(n)});ba=sub(bare_a,{induction:var(n)});bz=sub(bare_z,{induction:var(n)})
                            context={'If':dict(condition=var(hole),on_true=ba,on_false=bz)}
                            use=lambda xs,ps,p=p,context=context:trans({'Sym':{'Substitute':dict(variable=hole,context=context,equality=ps[0])}},p)
                            rules.append((ba,bz,[],[dict(**{'from':ig,'to':{'Bool':True}})],use))
                body=self.equality(sub(a,{induction:bound}),sub(z,{induction:bound}),local,rules,hypotheses=hypotheses)
                cases.append(dict(bindings=bindings,proof=body))
            proof={('GeneralizedInduction'if generalize else'Induction'):dict(variable=induction,**({'generalize':list(generalize)}if generalize else{}),**{'from':a,'to':z},cases=cases)}
        else:proof=self.equality(a,z,env)
        identity=self.add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
        self.register(identity)
        if guard is not None:
            context={'If':dict(condition=var(hole),on_true=bare_a,on_false=bare_z)}
            proof=trans({'Sym':{'Substitute':dict(variable=hole,context=context,equality={'Hypothesis':0})}},{'Use':dict(theorem=identity,arguments=[var(n)for n,_ in params],premises=[])})
            conditional=self.add({'Theorem':dict(params=params,conditions=[dict(**{'from':guard,'to':{'Bool':True}})],**{'from':bare_a,'to':bare_z},proof=proof)})
            self.register(conditional)
            return conditional
        return identity
