"""Untrusted structural instantiation of arbitrary first-order database laws.
No theorem-name or target whitelist. The kernel's Instance rule must check every
sort, function, definition mapping and all instantiated premises independently.
"""
import copy

class Matcher:
    def __init__(self,objects,actual):
        self.objects,self.actual=objects,actual;self.sorts={};self.functions={};self.definitions={};self.active=set()
    def declaration(self,ident):
        return self.objects[ident]['payload']['declaration']
    def sort(self,pattern,actual):
        if pattern==actual:return True
        if not isinstance(pattern,dict)or 'Data'not in pattern:return False
        ident=pattern['Data'];d=self.declaration(ident)
        if 'AbstractSort'in d:
            if ident in self.sorts:return self.sorts[ident]==actual
            self.sorts[ident]=copy.deepcopy(actual);return True
        if not isinstance(actual,dict)or 'Data'not in actual:return False
        return self.definition(ident,actual['Data'])
    def definition(self,pattern,actual):
        if pattern==actual:return True
        if pattern in self.definitions:return self.definitions[pattern]==actual
        if (pattern,actual)in self.active:return True
        a=self.declaration(pattern);b=self.actual.get(actual,{}).get('payload',{}).get('declaration',{})
        if 'AbstractFunction'in a:
            if 'Function'not in b:return False
            f,g=a['AbstractFunction'],b['Function']
            if len(f['params'])!=len(g['params'])or not self.sort(f['result'],g['result']):return False
            if not all(self.sort(x[1],y[1])for x,y in zip(f['params'],g['params'])):return False
            names=[n for n,_ in f['params']];lam=dict(params=names,body={'Call':dict(function=actual,arguments=[{'Var':n}for n in names])})
            if pattern in self.functions:return self.functions[pattern]==lam
            self.functions[pattern]=lam;return True
        if set(a)!=set(b):return False
        self.active.add((pattern,actual));self.definitions[pattern]=actual
        if 'Datatype'in a:
            x,y=a['Datatype']['constructors'],b['Datatype']['constructors']
            valid=len(x)==len(y)and all(cx['name']==cy['name']and len(cx['fields'])==len(cy['fields'])and all(self.sort(f,g)for f,g in zip(cx['fields'],cy['fields']))for cx,cy in zip(x,y))
        elif 'Function'in a:
            x,y=a['Function'],b['Function'];variables={}
            valid=len(x['params'])==len(y['params'])and x['recursive']==y['recursive']and self.sort(x['result'],y['result'])
            for (n,t),(m,u)in zip(x['params'],y['params']):
                valid=valid and self.sort(t,u);variables[n]={'Var':m}
            valid=valid and self.term(x['body'],y['body'],set(),{},variables)
        else:valid=False
        self.active.remove((pattern,actual))
        if not valid:self.definitions.pop(pattern,None)
        return valid
    def term(self,pattern,actual,parameters,bindings,scope=None):
        scope={}if scope is None else scope
        if isinstance(pattern,dict)and set(pattern)=={'Var'}:
            name=pattern['Var']
            if name in scope:return scope[name]==actual
            if name in parameters:
                if name in bindings:return bindings[name]==actual
                bindings[name]=copy.deepcopy(actual);return True
        if type(pattern)!=type(actual):return False
        if isinstance(pattern,list):return len(pattern)==len(actual)and all(self.term(a,b,parameters,bindings,scope)for a,b in zip(pattern,actual))
        if not isinstance(pattern,dict):return pattern==actual
        if pattern.keys()!=actual.keys():return False
        if 'Call'in pattern:
            a,b=pattern['Call'],actual['Call']
            return self.definition(a['function'],b['function'])and self.term(a['arguments'],b['arguments'],parameters,bindings,scope)
        if 'Construct'in pattern:
            a,b=pattern['Construct'],actual['Construct']
            return a['constructor']==b['constructor']and self.definition(a['datatype'],b['datatype'])and self.term(a['arguments'],b['arguments'],parameters,bindings,scope)
        if 'Match'in pattern:
            a,b=pattern['Match'],actual['Match']
            if not self.term(a['scrutinee'],b['scrutinee'],parameters,bindings,scope)or len(a['branches'])!=len(b['branches']):return False
            for x,y in zip(a['branches'],b['branches']):
                if len(x['bindings'])!=len(y['bindings']):return False
                local={**scope,**{n:{'Var':m}for n,m in zip(x['bindings'],y['bindings'])}}
                if not self.term(x['body'],y['body'],parameters,bindings,local):return False
            return True
        return all(self.term(pattern[k],actual[k],parameters,bindings,scope)for k in pattern)
    def instantiate(self,term):
        if isinstance(term,list):return [self.instantiate(x)for x in term]
        if not isinstance(term,dict):return self.definitions.get(term,self.sorts.get(term,term))if isinstance(term,str)else term
        if set(term)=={'Data'}and term['Data']in self.sorts:return copy.deepcopy(self.sorts[term['Data']])
        if 'Call'in term and term['Call']['function']in self.functions:
            from producers.point_delta import sub
            lam=self.functions[term['Call']['function']]
            return sub(lam['body'],dict(zip(lam['params'],[self.instantiate(a)for a in term['Call']['arguments']])))
        return {k:self.instantiate(v)for k,v in term.items()}
    def complete(self,dependencies):
        """Every abstract declaration in the theorem closure needs a mapping.
        Unsupported assumptions are explicitly declined, never asserted true."""
        for ident,obj in dependencies.items():
            d=obj['payload'].get('declaration',{})
            if 'AbstractSort'in d and ident not in self.sorts:return False
            if 'AbstractFunction'in d and ident not in self.functions:return False
            if 'Assumption'in d:return False
        return True

def prove(goal,objects,actual,work=None,active=None,depth=0):
    """Generic theorem instantiation for conditional endpoint propositions.
    Work and proof nesting are resource guards. Unknown conditions stay as
    ordinary conversion obligations and are never promoted to assumptions.
    """
    from ink_knowledge import canonical,identity
    from producers.point_delta import sub
    from producers.action_replacement import convert
    work=[4096]if work is None else work;active=set()if active is None else active
    digest=identity(goal)
    if work[0]<=0 or digest in active or depth>=128:return convert(goal['from'],goal['to']),set()
    active=active|{digest}
    for ident,obj in objects.items():
        law=obj['payload'].get('declaration',{}).get('Theorem')
        if law is None:continue
        work[0]-=1
        if work[0]<0:break
        matcher=Matcher(objects,actual);bindings={}
        if not matcher.term(law['from'],goal['from'],set(dict(law['params'])),bindings)or set(bindings)!=set(dict(law['params'])):continue
        if sub(matcher.instantiate(law['to']),bindings)!=goal['to']:continue
        closure=set();pending=[ident]
        while pending:
            i=pending.pop()
            if i in closure:continue
            closure.add(i);pending.extend(objects[i]['dependencies'])
        if not matcher.complete({i:objects[i]for i in closure}):continue
        premises=[];used={ident}
        for condition in law['conditions']:
            proof,dependencies=prove(dict(**{'from':sub(matcher.instantiate(condition['from']),bindings),'to':sub(matcher.instantiate(condition['to']),bindings)}),objects,actual,work,active,depth+1)
            premises.append(proof);used.update(dependencies)
        fields=dict(theorem=ident,arguments=[bindings[n]for n,_ in law['params']],premises=premises)
        proof={'Instance':dict(fields,sorts=matcher.sorts,functions=matcher.functions,definitions=matcher.definitions,assumptions={})}if matcher.sorts or matcher.functions or matcher.definitions else{'Use':fields}
        return proof,used
    return convert(goal['from'],goal['to']),set()
