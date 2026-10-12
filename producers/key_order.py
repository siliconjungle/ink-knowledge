"""Source-derived key operators and ordinary structural/scalar order proofs.

No producer assertion is an ordering axiom. Every emitted implication is checked
by the inductive equality kernel, including lexicographic recursion and scalar
leaves. Frozen scalar certificates make cold proposal generation solver-free.
"""
import hashlib,json,os,subprocess,tempfile
from pathlib import Path
from ink_knowledge import canonical
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import sub,normal,binary,choice
from producers.state_laws import replace


class Order:
    def __init__(self,table,objects,add,fun):
        self.objects,self.add=objects,add
        get=objects[table['get']]['payload']['declaration']['Function']
        insert=objects[table['insert']]['payload']['declaration']['Function']
        self.sort=get['params'][1][1]
        def operator(declaration):
            branch=declaration['body']['Match']['branches'][1]
            return sub(branch['body']['If']['condition'],{
                declaration['params'][1][0]:var('order_left'),
                branch['bindings'][0]:var('order_right')})
        self.equal_id=fun('key_equal',[['order_left',self.sort],['order_right',self.sort]],'Bool',operator(get))
        self.less_id=fun('key_less',[['order_left',self.sort],['order_right',self.sort]],'Bool',operator(insert))
        self.kind=table.get('key_type','U64')
        if self.kind=='Bool':self.bottom={'Bool':False};self.top={'Bool':True}
        elif self.kind=='I32':self.bottom={'U64':1<<31};self.top={'U64':(1<<31)-1}
        elif self.sort=='U64':self.bottom={'U64':0};self.top={'U64':(1<<32)-1 if self.kind=='U32' else (1<<64)-1}
        else:
            d=objects[self.sort['Data']]['payload']['declaration']['Datatype']
            self.bottom=cons(self.sort['Data'],0,[{'U64':0} for _ in d['constructors'][0]['fields']])
            # Strings have no finite greatest value. An empty child's bottom is
            # still a conservative lower bound; empty enumeration is preserved.
            self.top=self.bottom
        self.cache={};self.serial=0
    def less(self,a,z):return binary('<',a,z) if self.kind=='U64' else call(self.less_id,[a,z])
    def equal(self,a,z):return binary('==',a,z) if self.kind=='U64' else call(self.equal_id,[a,z])
    def greater(self,a,z):return self.less(z,a)
    def minimum(self,a,z):return choice(self.less(a,z),a,z)
    def maximum(self,a,z):return choice(self.less(a,z),z,a)
    def within(self,x,lo,hi):return binary('&&',choice(self.less(x,lo),{'Bool':False},{'Bool':True}),choice(self.less(hi,x),{'Bool':False},{'Bool':True}))
    def scalar(self,params,a,z,conditions,proofs=()):
        """Factor opaque Boolean calls as parameters, never as assumed facts."""
        atoms=[];atom_names=[];occupied={n for n,_ in params}
        def abstract(t):
            if any(k in t for k in ['Var','U64','Bool']):return t
            if 'Binary' in t:
                x=t['Binary'];return binary(x['op'],abstract(x['left']),abstract(x['right']))
            if 'If' in t:
                x=t['If'];return choice(abstract(x['condition']),abstract(x['on_true']),abstract(x['on_false']))
            if 'Call' in t and self.objects[t['Call']['function']]['payload']['declaration']['Function']['result']=='Bool':
                if t not in atoms:
                    atoms.append(t);n='order_atom_'+str(len(atoms)-1)
                    while n in occupied:n+='_'
                    atom_names.append(n);occupied.add(n)
                return var(atom_names[atoms.index(t)])
            raise ValueError('order scalar needs structural elimination')
        original_a,original_z=a,z;a,z=normal(a,self.objects),normal(z,self.objects)
        cs=[dict(**{'from':normal(c['from'],self.objects),'to':normal(c['to'],self.objects)}) for c in conditions]
        aa,zz=abstract(a),abstract(z);cc=[dict(**{'from':abstract(c['from']),'to':abstract(c['to'])}) for c in cs]
        from producers.cache_maintenance import variables
        used=set().union(*(variables(t) for t in [aa,zz,*[x for c in cc for x in c.values()]]))
        ps=[[n,s] for n,s in params if n in used]
        ps += [[n,'Bool'] for n in atom_names]
        if any(s not in ['U64','Bool'] for _,s in ps):raise ValueError('uneliminated key sort')
        goal=dict(params=ps,conditions=cc,**{'from':aa,'to':zz})
        marker=hashlib.sha256(canonical(goal)).hexdigest()
        if marker not in self.cache:
            frozen=Path(__file__).with_name('data')/'key-order'/f'{marker}.json'
            cache=Path(__file__).resolve().parents[1]/'build/key-order'/f'{marker}.json'
            if frozen.exists() or cache.exists():p=json.loads((frozen if frozen.exists() else cache).read_text())
            else:
                compiler=Path(os.environ.get('INK_COMPILER','target/debug/ink')).resolve()
                with tempfile.TemporaryDirectory(prefix='ink-order-') as tmp:
                    d=Path(tmp);(d/'goal.json').write_bytes(canonical(goal))
                    result=subprocess.run([str(compiler),'bitvector-obligation',str(d/'goal.json'),'-o',str(d/'cnf.json')],capture_output=True,text=True,check=True)
                    from producers.bitvector_proofs import certificate
                    p={'BitVector':dict(**{'from':aa,'to':zz},hypotheses=list(range(len(cc))),certificate=certificate(json.loads((d/'cnf.json').read_text())))}
                cache.parent.mkdir(parents=True,exist_ok=True);cache.write_bytes(canonical(p)+b'\n')
            self.cache[marker]=self.add({'Theorem':dict(**goal,proof=p)})
        premises=list(proofs) if proofs else [{'Hypothesis':i} for i in range(len(conditions))]
        premises=[trans(convert(cs[i]['from'],c['from']),p,convert(c['to'],cs[i]['to'])) for i,(c,p) in enumerate(zip(conditions,premises))]
        arguments=dict(zip(atom_names,atoms))
        use={'Use':dict(theorem=self.cache[marker],arguments=[arguments[n] if n in arguments else var(n) for n,_ in ps],premises=premises)}
        return trans(convert(original_a,a),use,convert(z,original_z))
    def prove(self,params,a,z,conditions=()):
        # Quantify premises inside the induction proposition. Fixed hypotheses
        # must never be generalized over different recursive tail values.
        whole=a
        for c in reversed(conditions):whole=choice(binary('==',c['from'],c['to']),whole,z)
        original=whole
        env=dict(params);keys=[n for n,s in params if s==self.sort]
        if self.sort in ['U64','Bool']:return self.scalar(params,a,z,conditions)
        datatype=self.sort['Data'];constructors=self.objects[datatype]['payload']['declaration']['Datatype']['constructors']
        recursive=any('SelfType' in c['fields'] for c in constructors)
        def leaf(left,right,local,facts,ih,depth=0):
            if depth>18:raise ValueError('key order proof split limit')
            nl,nr=normal(left,self.objects),normal(right,self.objects)
            def simplify(t):
                out=t;p=convert(t,t)
                for x,y,i in facts:
                    xx=normal(x,self.objects);updated=replace(out,xx,y)
                    if updated!=out:
                        p=trans(p,{'Substitute':dict(variable='order_hole',context=replace(out,xx,var('order_hole')),equality={'Hypothesis':i})},convert(updated,normal(updated,self.objects)));out=normal(updated,self.objects)
                return out,p
            sl,pl=simplify(nl);sr,pr=simplify(nr)
            if sl==sr:return trans(convert(left,nl),pl,convert(sl,sr),{'Sym':pr},convert(nr,right))
            cs=[dict(**{'from':x,'to':y}) for x,y,_ in facts];proofs=[{'Hypothesis':i} for _,_,i in facts]
            if ih:
                x,y,p=ih;nx,ny=normal(x,self.objects),normal(y,self.objects)
                sx,px=simplify(nx);sy,py=simplify(ny)
                cs.append(dict(**{'from':sx,'to':sy}))
                proofs.append(trans({'Sym':px},convert(nx,x),p,convert(y,ny),py))
            try:
                p=self.scalar(list(local.items()),sl,sr,cs,proofs)
                return trans(convert(left,nl),pl,p,{'Sym':pr},convert(nr,right))
            except (ValueError,subprocess.CalledProcessError):pass
            def choices(t):
                if isinstance(t,dict):
                    if 'If' in t:
                        x=t['If'];yield from choices(x['condition']);yield x['condition']
                    for k,v in t.items():
                        if k!='If':yield from choices(v)
                        elif isinstance(v,dict):
                            yield from choices(v['on_true']);yield from choices(v['on_false'])
                elif isinstance(t,list):
                    for x in t:yield from choices(x)
            condition=next((c for c in choices([sl,sr]) if not any(normal(x,self.objects)==c for x,_,_ in facts)),None)
            if condition is None:raise ValueError('cannot prove source key order: '+str((sl,sr))[:1200])
            index=len(facts)
            return {'BoolSplit':dict(condition=condition,**{'from':left,'to':right},**{name:leaf(left,right,local,[*facts,(condition,{'Bool':flag},index)],ih,depth+1) for name,flag in [('on_false',False),('on_true',True)]})}
        def eliminate(i,left,right,local,bindings):
            if i==len(keys):
                ih=None
                if recursive and all(len(bindings[n])==2 for n in keys):
                    mapping={n:var(bindings[n][1]) for n in keys};ih=(sub(original,mapping),sub(z,mapping),{'GeneralizedHypothesis':dict(index=0,arguments=[mapping[n] for n in keys[1:]])})
                return leaf(left,right,local,[],ih)
            name=keys[i];cases=[]
            for j,c in enumerate(constructors):
                ns=[f'order_{i}_{j}_{k}' for k in range(len(c['fields']))];value=cons(datatype,j,[var(n) for n in ns]);mapping={name:value}
                sorts=[self.sort if s=='SelfType' else s for s in c['fields']]
                cases.append(dict(bindings=ns,proof=eliminate(i+1,sub(left,mapping),sub(right,mapping),{**local,**dict(zip(ns,sorts))},{**bindings,name:ns})))
            kind='GeneralizedInduction' if i==0 and recursive else 'Cases'
            return {kind:dict(variable=name,**({'generalize':keys[1:]} if kind=='GeneralizedInduction' else {}),**{'from':left,'to':right},cases=cases)}
        p=eliminate(0,whole,z,env,{})
        ident=self.add({'Theorem':dict(params=params,conditions=[],**{'from':whole,'to':z},proof=p)})
        if not conditions:return {'Use':dict(theorem=ident,arguments=[var(n) for n,_ in params],premises=[])}
        current=whole;start=convert(whole,whole)
        for i,c in enumerate(conditions):
            test=binary('==',c['from'],c['to']);following=replace(current,test,{'Bool':True})
            equality={'Binary':dict(op='==',left={'Hypothesis':i},right={'Refl':c['to']})}
            # Equality reflexivity is scalar, so its Boolean true result is checked.
            scalar=self.scalar([],binary('==',c['to'],c['to']),{'Bool':True},[])
            truth=trans(equality,scalar)
            start=trans(start,{'Substitute':dict(variable='order_hole',context=replace(current,test,var('order_hole')),equality=truth)},convert(following,normal(following,self.objects)));current=normal(following,self.objects)
        return trans({'Sym':start},{'Use':dict(theorem=ident,arguments=[var(n) for n,_ in params],premises=[])})
