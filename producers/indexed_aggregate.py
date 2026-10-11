#!/usr/bin/env python3
"""Source-bound ordered sequence trees with database-defined cached aggregates.

The representation preserves order and duplicate keys; it does not assume that
an arbitrary logical table is already a sorted, unique native map.
"""
import argparse,hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from ink_knowledge import Store,identity,canonical
from ink_knowledge.store import entry
from producers.action_replacement import var,call,cons,convert,trans
from producers.representations import refs,match
from producers.point_delta import binary,choice,sub,normal
from producers.state_laws import derive,replace
from producers.aggregate_delta import setup

def definitions(model, *, table_index=0, aggregate_factory=None, layout_only=False):
    objects=dict(model['objects']);names={}
    def add(decl,extra=(),name=None):
        payload={'declaration':decl};body=next(iter(decl.values()))
        # Match scrutinees may infer a datatype from a called signature.
        # Import exactly that type graph, rather than the whole datatype catalog.
        inferred=set();pending=list(refs(payload)|set(extra))
        while pending:
            ref=pending.pop();d=objects.get(ref,{}).get('payload',{}).get('declaration',{})
            if 'Datatype' in d:
                if ref in inferred:continue
                inferred.add(ref);pending.extend(refs(d['Datatype']))
            else:
                for kind in ['Function','AbstractFunction','Theorem']:
                    if kind in d:pending.extend(refs([d[kind].get('params',[]),d[kind].get('result')]))
        extra=(*extra,*inferred)
        obj=entry('theorem' if 'Theorem'in decl else 'definition','first-order-inductive-equality-v1',payload,refs(payload)|set(extra),parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]));i=identity(obj);objects[i]=obj
        if name:names[name]=i
        return i
    def fun(name,params,result,body,recursive=None):return add({'Function':dict(params=params,result=result,body=body,recursive=recursive)},name=name)
    def endpoints(p,conditions):
        if 'Convert' in p:return p['Convert']['from'],p['Convert']['to']
        if 'Refl' in p:return p['Refl'],p['Refl']
        if 'Hypothesis' in p:x=conditions[p['Hypothesis']];return x['from'],x['to']
        if 'Use' in p:
            x=p['Use'];d=objects[x['theorem']]['payload']['declaration']['Theorem'];mapping=dict(zip([n for n,_ in d['params']],x['arguments']));return sub(d['from'],mapping),sub(d['to'],mapping)
        if 'Sym' in p:a,z=endpoints(p['Sym'],conditions);return z,a
        if 'Trans' in p:return endpoints(p['Trans'][0],conditions)[0],endpoints(p['Trans'][1],conditions)[1]
        for k in ['Call','Construct']:
            if k in p:
                x=p[k];ps=[endpoints(q,conditions) for q in x['arguments']];return tuple({k:{**x,'arguments':[q[j] for q in ps]}} for j in [0,1])
        if 'Substitute' in p:
            x=p['Substitute'];a,z=endpoints(x['equality'],conditions);return sub(x['context'],{x['variable']:a}),sub(x['context'],{x['variable']:z})
        if 'Binary' in p:
            x=p['Binary'];a,z=endpoints(x['left'],conditions),endpoints(x['right'],conditions);return binary(x['op'],a[0],z[0]),binary(x['op'],a[1],z[1])
        for k in ['BoolSplit','BoolCases','Induction','BitVector']:
            if k in p:return p[k]['from'],p[k]['to']
        raise ValueError('cannot factor proof '+str(p)[:100])
    def factor_proof(p,params,conditions):
        def theorem(x,proof,ps=params,cs=conditions):
            i=add({'Theorem':dict(params=ps,conditions=list(cs),**{'from':x['from'],'to':x['to']},proof=proof)})
            return {'Use':dict(theorem=i,arguments=[var(n) for n,_ in ps],premises=[{'Hypothesis':j} for j in range(len(cs))])}
        if 'BoolSplit' in p:
            x=p['BoolSplit'];bs={}
            for key,b in [('on_false',False),('on_true',True)]:
                bs[key]=factor_proof(x[key],params,[*conditions,{'from':x['condition'],'to':{'Bool':b}}])
            return theorem(x,{'BoolSplit':{**x,**bs}})
        if 'Induction' in p:
            x=p['Induction'];env=dict(params);sort=env[x['variable']];data=sort['Data'];constructors=objects[data]['payload']['declaration']['Datatype']['constructors'];cs=[]
            for j,(c,decl) in enumerate(zip(x['cases'],constructors)):
                sorts=[sort if ty=='SelfType' else ty for ty in decl['fields']];local=[(n,ty) for n,ty in params if n!=x['variable']]+list(zip(c['bindings'],sorts))
                value=cons(data,j,[var(n) for n in c['bindings']]);goal={k:sub(x[k],{x['variable']:value}) for k in ['from','to']}
                hypotheses=[*conditions,*({k:sub(x[k],{x['variable']:var(n)}) for k in ['from','to']} for n,ty in zip(c['bindings'],sorts) if ty==sort)]
                body=factor_proof(c['proof'],local,hypotheses);cs.append({**c,'proof':theorem(goal,body,local,hypotheses)})
            return {'Induction':{**x,'cases':cs}}
        if 'Trans' in p:
            body={'Trans':[factor_proof(x,params,conditions) for x in p['Trans']]}
            if len(json.dumps(p))>2000:
                a,z=endpoints(p,conditions);return theorem({'from':a,'to':z},body)
            return body
        if 'Use' in p:
            body={'Use':{**p['Use'],'premises':[factor_proof(q,params,conditions) for q in p['Use']['premises']]}}
            if len(json.dumps(p))>1000:
                a,z=endpoints(p,conditions);return theorem({'from':a,'to':z},body)
            return body
        if 'Sym' in p:return {'Sym':factor_proof(p['Sym'],params,conditions)}
        if 'Substitute' in p:
            body={'Substitute':{**p['Substitute'],'equality':factor_proof(p['Substitute']['equality'],params,conditions)}}
            if len(json.dumps(p))>1000:
                a,z=endpoints(p,conditions);return theorem({'from':a,'to':z},body)
            return body
        for kind in ['Call','Construct']:
            if kind in p:return {kind:{**p[kind],'arguments':[factor_proof(q,params,conditions) for q in p[kind]['arguments']]}}
        return p
    def law(name,params,a,z,p,conditions=()):return add({'Theorem':dict(params=params,conditions=list(conditions),**{'from':a,'to':z},proof=factor_proof(p,params,list(conditions)) if name is None or name.startswith(('rotate_','balance_')) else p)},name=name)
    def induction(name,params,a,z,cases,conditions=()):
        return law(name,params,a,z,{'Induction':dict(variable=params[0][0],**{'from':a,'to':z},cases=[dict(bindings=bindings,proof=p) for bindings,p in cases])},conditions)
    if not layout_only and len(model['tables'])!=1:raise ValueError('whole-action legacy producer requires one table')
    table=model['tables'][table_index];rows=table['datatype'];R={'Data':rows};row=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1];nil=cons(rows,0,[])
    aggregates=aggregate_factory(model,table,add,objects) if aggregate_factory else [setup(model,model['actions'][query],add,objects) for query in ['total_query','count_query']]
    sum_sort=aggregates[0].get('sort','U64'); count_sort=aggregates[1].get('sort','U64')
    opaque=tuple(f for a in aggregates for f in a.get('opaque',[]))
    from producers.state_laws import derive as base_derive
    from producers.point_delta import normal as base_normal
    def normal(t,objs):return base_normal(t,objs,opaque=opaque)
    def derive(*args,**kwargs):return base_derive(*args,**kwargs,opaque=opaque)
    combine=lambda label,a,z:aggregates[0 if label=='sum' else 1].get('combine',lambda x,y:binary('+',x,y))(a,z)
    for label,a in zip(['sum','count'],aggregates):
        names[label+'_contribution']=a['contribution'];names[label+'_fold']=a['fold'];names[label+'_fusion']=a['fusion'];names.update({label+'_'+k+'_delta':v for k,v in a['updates'].items()})
    append=fun('append',[['left',R],['right',R]],R,match(var('left'),[([],var('right')),(['key','row','tail'],cons(rows,1,[var('key'),var('row'),{'SelfCall':[var('tail'),var('right')]}]))]),0)
    cat=lambda a,b:call(append,[a,b])
    tree=add({'Datatype':dict(constructors=[dict(name='Empty',fields=[]),dict(name='Leaf',fields=['U64',row]),dict(name='Branch',fields=['SelfType','SelfType','U64','U64',sum_sort,count_sort,'U64'])])},name='tree');T={'Data':tree};empty=cons(tree,0,[]);leaf=lambda k,v:cons(tree,1,[k,v]);node=lambda l,r,lo,hi,s,c,h:cons(tree,2,[l,r,lo,hi,s,c,h]);bindings=['left','right','lo','hi','sum','count','height']
    fields={}
    for name,leaf_value,node_value,empty_value in [
        ('low',var('key'),var('lo'),(1<<64)-1),('high',var('key'),var('hi'),0),
        ('sum',call(aggregates[0]['contribution'],[var('key'),var('row')] if aggregates[0].get('contribution_keys') else [var('row')]),var('sum'),0),
        ('count',call(aggregates[1]['contribution'],[var('row')]),var('count'),0),('height',{'U64':1},var('height'),0)]:
        field_bindings=['field_'+name+'_'+n for n in bindings];leaf_bindings=['field_'+name+'_key','field_'+name+'_row']
        fields[name]=fun(name,[['tree',T]],sum_sort if name=='sum' else count_sort if name=='count' else 'U64',match(var('tree'),[([],aggregates[0].get('empty',{'U64':empty_value}) if name=='sum' else {'U64':empty_value}),(leaf_bindings,sub(leaf_value,{'key':var(leaf_bindings[0]),'row':var(leaf_bindings[1])})),(field_bindings,sub(node_value,dict(zip(bindings,map(var,field_bindings)))))]))
    field=lambda n,t:call(fields[n],[t]);minimum=lambda a,b:choice(binary('<',a,b),a,b);maximum=lambda a,b:choice(binary('<',a,b),b,a)
    smart=fun('branch',[['left',T],['right',T]],T,node(var('left'),var('right'),minimum(field('low',var('left')),field('low',var('right'))),maximum(field('high',var('left')),field('high',var('right'))),combine('sum',field('sum',var('left')),field('sum',var('right'))),combine('count',field('count',var('left')),field('count',var('right'))),binary('+',maximum(field('height',var('left')),field('height',var('right'))),{'U64':1})))
    branch=lambda l,r:call(smart,[l,r])
    repair=fun('repair',[['tree',T]],T,match(var('tree'),[([],empty),(['key','row'],leaf(var('key'),var('row'))),(bindings,branch({'SelfCall':[var('left')]},{'SelfCall':[var('right')]}))]),0)
    fix=lambda t:call(repair,[t])
    decode=fun('decode',[['tree',T]],R,match(var('tree'),[([],nil),(['key','row'],cons(rows,1,[var('key'),var('row'),nil])),(bindings,cat({'SelfCall':[var('left')]},{'SelfCall':[var('right')]}))]),0)
    logical=lambda t:call(decode,[t]);bound=node(*map(var,bindings));treecases=[([],empty),(['key','row'],leaf(var('key'),var('row'))),(bindings,bound)]
    a,z=fix(fix(var('tree'))),fix(var('tree'))
    induction('repair_idempotent',[['tree',T]],a,z,[(ns,derive(replace(a,var('tree'),t),replace(z,var('tree'),t),objects,[(fix(fix(var('left'))),fix(var('left'))),(fix(fix(var('right'))),fix(var('right')))] if len(ns)>2 else ())) for ns,t in treecases])
    a,z=logical(fix(var('tree'))),logical(var('tree'))
    induction('repair_preserves_rows',[['tree',T]],a,z,[(ns,derive(replace(a,var('tree'),t),replace(z,var('tree'),t),objects,[(logical(fix(var('left'))),logical(var('left'))),(logical(fix(var('right'))),logical(var('right')))] if len(ns)>2 else ())) for ns,t in treecases])
    # Associativity preserves arbitrary sequence order through rotations.
    a,z=cat(cat(var('left'),var('middle')),var('right')),cat(var('left'),cat(var('middle'),var('right')))
    boundrows=cons(rows,1,[var('key'),var('row'),var('tail')]);tail_a=replace(a,var('left'),var('tail'));tail_z=replace(z,var('left'),var('tail'))
    induction('append_associative',[['left',R],['middle',R],['right',R]],a,z,[([],convert(replace(a,var('left'),nil),replace(z,var('left'),nil))),(['key','row','tail'],derive(replace(a,var('left'),boundrows),replace(z,var('left'),boundrows),objects,[(tail_a,tail_z)]))])
    def rewrite_derive(a,z,hypotheses=(),rewrites=()):
        def simplify(t):
            current=normal(t,objects);proof=convert(t,current)
            for x,y,p in rewrites:
                x,y=normal(x,objects),normal(y,objects);updated=replace(current,x,y)
                if updated!=current:
                    context=replace(current,x,var('rewrite_hole'));following=normal(updated,objects)
                    proof=trans(proof,{'Substitute':dict(variable='rewrite_hole',context=context,equality=p)},convert(updated,following));current=following
            return current,proof
        aa,pa=simplify(a);zz,pz=simplify(z)
        return trans(pa,derive(aa,zz,objects,hypotheses),{'Sym':pz})
    def use(i,args,premises=()):return {'Use':dict(theorem=i,arguments=args,premises=list(premises))}
    target=var('target');new=var('new');get_sort=objects[table['get']]['payload']['declaration']['Function']['result'];option=get_sort['Data'];none=cons(option,0,[])
    chooseget=fun('first_present',[['first',get_sort],['second',get_sort]],get_sort,match(var('first'),[([],var('second')),(['value'],cons(option,1,[var('value')]))]))
    either=lambda a,b:call(chooseget,[a,b]);get=lambda r:call(table['get'],[r,target])
    a,z=get(cat(var('left'),var('right'))),either(get(var('left')),get(var('right')))
    getcat=induction('lookup_append',[['left',R],['right',R],['target','U64']],a,z,[([],convert(replace(a,var('left'),nil),replace(z,var('left'),nil))),(['key','row','tail'],derive(replace(a,var('left'),boundrows),replace(z,var('left'),boundrows),objects,[(replace(a,var('left'),var('tail')),replace(z,var('left'),var('tail')))]))])
    rawget=fun('lookup_unpruned',[['tree',T],['target','U64']],get_sort,match(var('tree'),[([],none),(['key','row'],choice(binary('==',target,var('key')),cons(option,1,[var('row')]),none)),(bindings,either({'SelfCall':[var('left'),target]},{'SelfCall':[var('right'),target]}))]),0)
    lookup=lambda t:call(rawget,[t,target]);a,z=lookup(var('tree')),get(logical(var('tree')))
    node_from=get(cat(logical(var('left')),logical(var('right'))));node_to=either(get(logical(var('left'))),get(logical(var('right'))))
    getproof=induction('lookup_preserves_rows',[['tree',T],['target','U64']],a,z,[(ns,rewrite_derive(replace(a,var('tree'),t),replace(z,var('tree'),t),[(lookup(var('left')),get(logical(var('left')))),(lookup(var('right')),get(logical(var('right'))))] if len(ns)>2 else (),[(node_from,node_to,use(getcat,[logical(var('left')),logical(var('right')),target]))] if len(ns)>2 else ())) for ns,t in treecases])
    raw_updates={}
    for label in ['remove','replace']:
        rest=[['target','U64']]+([['new',row]] if label=='replace' else [])
        args=[target]+([new] if label=='replace' else []);op=lambda r:call(table[label],[r,*args])
        a,z=op(cat(var('left'),var('right'))),cat(op(var('left')),op(var('right')))
        catlaw=induction(label+'_append',[['left',R],['right',R],*rest],a,z,[([],convert(replace(a,var('left'),nil),replace(z,var('left'),nil))),(['key','row','tail'],derive(replace(a,var('left'),boundrows),replace(z,var('left'),boundrows),objects,[(replace(a,var('left'),var('tail')),replace(z,var('left'),var('tail')))]))])
        changed=empty if label=='remove' else leaf(var('key'),new)
        leafbody=choice(binary('==',target,var('key')),changed,leaf(var('key'),var('row')))
        rawop=fun(label+'_unpruned',[['tree',T],*rest],T,match(var('tree'),[([],empty),(['key','row'],leafbody),(bindings,branch({'SelfCall':[var('left'),*args]},{'SelfCall':[var('right'),*args]}))]),0)
        raw_updates[label]=rawop
        update=lambda t:call(rawop,[t,*args]);a,z=logical(update(var('tree'))),op(logical(var('tree')))
        node_from=op(cat(logical(var('left')),logical(var('right'))));node_to=cat(op(logical(var('left'))),op(logical(var('right'))))
        induction(label+'_preserves_rows',[['tree',T],*rest],a,z,[(ns,rewrite_derive(replace(a,var('tree'),t),replace(z,var('tree'),t),[(logical(update(var('left'))),op(logical(var('left')))),(logical(update(var('right'))),op(logical(var('right'))))] if len(ns)>2 else (),[(node_from,node_to,use(catlaw,[logical(var('left')),logical(var('right')),*args]))] if len(ns)>2 else ())) for ns,t in treecases])
    for label,aggregate in zip(['sum','count'],aggregates):
        total=lambda r:call(aggregate['fold'],[r]);arithmetic=aggregate['prove_arithmetic']
        a,z=total(cat(var('left'),var('right'))),combine(label,total(var('left')),total(var('right')))
        catlaw=induction(label+'_append',[['left',R],['right',R]],a,z,[([],derive(replace(a,var('left'),nil),replace(z,var('left'),nil),objects,leaf=arithmetic)),(['key','row','tail'],derive(replace(a,var('left'),boundrows),replace(z,var('left'),boundrows),objects,[(replace(a,var('left'),var('tail')),replace(z,var('left'),var('tail')))],leaf=arithmetic))])
        a,z=field(label,fix(var('tree'))),total(logical(var('tree')))
        node_from=total(cat(logical(var('left')),logical(var('right'))));node_to=combine(label,total(logical(var('left'))),total(logical(var('right'))))
        ps=[]
        for ns,t in treecases:
            aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t)
            if len(ns)>2:
                nz=normal(zz,objects);x,y=normal(node_from,objects),normal(node_to,objects);updated=replace(nz,x,y)
                p=trans(convert(zz,nz),{'Substitute':dict(variable='rewrite_hole',context=replace(nz,x,var('rewrite_hole')),equality=use(catlaw,[logical(var('left')),logical(var('right'))]))},convert(updated,normal(updated,objects)))
                q=derive(aa,updated,objects,[(field(label,fix(var('left'))),total(logical(var('left')))),(field(label,fix(var('right'))),total(logical(var('right'))))],leaf=arithmetic)
                ps.append((ns,trans(q,{'Sym':p})))
            else:ps.append((ns,derive(aa,zz,objects,leaf=arithmetic)))
        induction(label+'_repair_matches_rows',[['tree',T]],a,z,ps)
    # Scalar implications are ordinary bounded SAT/RUP theorems, not index rules.
    from producers.bitvector_proofs import certificate
    def scalar(name,params,a,z,conditions=()):
        goal=dict(params=params,conditions=list(conditions),**{'from':a,'to':z});key=hashlib.sha256(canonical(goal)).hexdigest();cache=Path(__file__).resolve().parents[1]/'build/index-word-laws';cache.mkdir(parents=True,exist_ok=True);cached=cache/(key+'.json')
        if cached.exists():proof=json.loads(cached.read_text())
        else:
            with tempfile.TemporaryDirectory(prefix='ink-index-word-') as tmp:
                d=Path(tmp);(d/'goal.json').write_text(json.dumps(goal));compiler=Path(os.environ.get('INK_COMPILER','target/debug/ink')).resolve()
                r=subprocess.run([str(compiler),'bitvector-obligation',str(d/'goal.json'),'-o',str(d/'cnf.json')],capture_output=True,text=True)
                if r.returncode:raise ValueError(r.stderr)
                proof={'BitVector':dict(**{'from':a,'to':z},hypotheses=list(range(len(conditions))),certificate=certificate(json.loads((d/'cnf.json').read_text())))}
            cached.write_text(json.dumps(proof)+'\n')
        return law(name,params,a,z,proof,conditions)
    def lifted(p,context):return {'Substitute':dict(variable='prune_hole',context=context,equality=p)}
    low=lambda t:binary('<',target,field('low',fix(t)));high=lambda t:binary('>',target,field('high',fix(t)))
    no_match={};bound_laws={};unequal_laws={}
    for label,guard,op,extreme in [('low',low,'<',minimum),('high',high,'>',maximum)]:
        x,y,w=map(var,['x','a','b']);truth={'Bool':True};false={'Bool':False};premise=binary(op,x,extreme(y,w))
        childlaws=[scalar(label+'_bounds_'+side,[['x','U64'],['a','U64'],['b','U64']],binary(op,x,child),truth,[{'from':premise,'to':truth}]) for side,child in [('left',y),('right',w)]]
        bound_laws[label]=childlaws
        unequal=scalar(label+'_excludes_equal',[['x','U64'],['a','U64']],binary('==',x,y),false,[{'from':binary(op,x,y),'to':truth}])
        unequal_laws[label]=unequal
        a,z=choice(guard(var('tree')),lookup(var('tree')),none),none;ps=[]
        for ns,t in treecases:
            aa=replace(a,var('tree'),t);g=guard(t);n=normal(aa,objects);body=lookup(t)
            if not ns:ps.append((ns,derive(aa,z,objects)));continue
            index=2 if len(ns)>2 else 0
            first=trans(convert(aa,n),lifted({'Hypothesis':index},replace(n,normal(g,objects),var('prune_hole'))),convert(replace(n,normal(g,objects),truth),body))
            if len(ns)>2:
                children=[]
                for j,child in enumerate(['left','right']):
                    cg=guard(var(child));eq=use(childlaws[j],[target,field(label,fix(var('left'))),field(label,fix(var('right')))],[{'Hypothesis':index}])
                    chosen=choice(cg,lookup(var(child)),none)
                    children.append(trans(convert(lookup(var(child)),choice(truth,lookup(var(child)),none)),{'Sym':lifted(eq,choice(var('prune_hole'),lookup(var(child)),none))},{'Hypothesis':j}))
                middle=trans(convert(body,either(lookup(var('left')),lookup(var('right')))),{'Call':dict(function=chooseget,arguments=children)},convert(either(none,none),none))
            else:
                eq=use(unequal,[target,var('key')],[{'Hypothesis':index}]);cmp=binary('==',target,var('key'))
                middle=trans(convert(body,choice(cmp,cons(option,1,[var('row')]),none)),lifted(eq,choice(var('prune_hole'),cons(option,1,[var('row')]),none)),convert(choice(false,cons(option,1,[var('row')]),none),none))
            false_case=trans(convert(aa,n),lifted({'Hypothesis':index},replace(n,normal(g,objects),var('prune_hole'))),convert(replace(n,normal(g,objects),false),none))
            case={'BoolSplit':dict(condition=g,**{'from':aa,'to':none},on_false=false_case,on_true=trans(first,middle))}
            ps.append((ns,case))
        no_match[label]=induction(label+'_pruning_safe',[['tree',T],['target','U64']],a,z,ps)
    outside=lambda t:binary('||',low(t),high(t));a,z=choice(outside(var('tree')),none,lookup(var('tree'))),lookup(var('tree'))
    def drop_branch(low_true,high_true):
        eqs=[(normal(low(var('tree')),objects),{'Bool':low_true},{'Hypothesis':0}),(normal(high(var('tree')),objects),{'Bool':high_true},{'Hypothesis':1})]
        current=normal(a,objects);proof=convert(a,current)
        for x,y,eq in eqs:
            updated=replace(current,x,y);proof=trans(proof,lifted(eq,replace(current,x,var('prune_hole'))),convert(updated,normal(updated,objects)));current=normal(updated,objects)
        if not low_true and not high_true:return trans(proof,convert(current,z))
        label='low' if low_true else 'high';g=low(var('tree')) if low_true else high(var('tree'));eq={'Hypothesis':0 if low_true else 1}
        chosen=choice(g,z,none)
        pruning=trans(convert(z,choice({'Bool':True},z,none)),{'Sym':lifted(eq,choice(var('prune_hole'),z,none))},use(no_match[label],[var('tree'),target]))
        return trans(proof,{'Sym':pruning})
    branches={}
    for low_true in [False,True]:branches['on_true' if low_true else 'on_false']={'BoolSplit':dict(condition=high(var('tree')),**{'from':a,'to':z},on_false=drop_branch(low_true,False),on_true=drop_branch(low_true,True))}
    drop=law('lookup_drop_pruning',[['tree',T],['target','U64']],a,z,{'BoolSplit':dict(condition=low(var('tree')),**{'from':a,'to':z},**branches)})
    # Literal indexed lookup inspects cached bounds before descending.
    raw_outside=lambda t:binary('||',binary('<',target,field('low',t)),binary('>',target,field('high',t)))
    indexed_get=fun('lookup',[['tree',T],['target','U64']],get_sort,choice(raw_outside(var('tree')),none,match(var('tree'),[([],none),(['key','row'],choice(binary('==',target,var('key')),cons(option,1,[var('row')]),none)),(bindings,either({'SelfCall':[var('left'),target]},{'SelfCall':[var('right'),target]}))])),0)
    fast=lambda t:call(indexed_get,[t,target]);a,z=fast(fix(var('tree'))),lookup(var('tree'));ps=[]
    for ns,t in treecases:
        aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t)
        intermediate=choice(outside(t),none,lookup(t));hyps=[(fast(fix(var('left'))),lookup(var('left'))),(fast(fix(var('right'))),lookup(var('right')))] if len(ns)>2 else ()
        ps.append((ns,trans(derive(aa,intermediate,objects,hyps),use(drop,[t,target]))))
    induction('indexed_lookup_preserves_rows',[['tree',T],['target','U64']],a,z,ps)
    for operation in ['remove','replace']:
        rest=[['target','U64']]+([['new',row]] if operation=='replace' else []);args=[target]+([new] if operation=='replace' else []);rawop=raw_updates[operation]
        update=lambda t:call(rawop,[t,*args]);a,z=fix(update(var('tree'))),update(fix(var('tree')))
        commute=induction(operation+'_repair_commutes',[['tree',T],*rest],a,z,[(ns,derive(replace(a,var('tree'),t),replace(z,var('tree'),t),objects,[(fix(update(var('left'))),update(fix(var('left')))),(fix(update(var('right'))),update(fix(var('right'))))] if len(ns)>2 else ())) for ns,t in treecases])
        unchanged={}
        for label,guard in [('low',low),('high',high)]:
            a,z=choice(guard(var('tree')),update(fix(var('tree'))),fix(var('tree'))),fix(var('tree'));ps=[]
            for ns,t in treecases:
                aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t);g=guard(t);n=normal(aa,objects);body=update(fix(t));index=2 if len(ns)>2 else 0
                first=trans(convert(aa,n),lifted({'Hypothesis':index},replace(n,normal(g,objects),var('prune_hole'))),convert(replace(n,normal(g,objects),{'Bool':True}),body))
                if len(ns)>2:
                    children=[]
                    for j,child in enumerate(['left','right']):
                        cg=guard(var(child));eq=use(bound_laws[label][j],[target,field(label,fix(var('left'))),field(label,fix(var('right')))],[{'Hypothesis':index}]);child_old=fix(var(child));child_new=update(child_old)
                        children.append(trans(convert(child_new,choice({'Bool':True},child_new,child_old)),{'Sym':lifted(eq,choice(var('prune_hole'),child_new,child_old))},{'Hypothesis':j}))
                    middle=trans(convert(body,branch(update(fix(var('left'))),update(fix(var('right'))))),{'Call':dict(function=smart,arguments=children)},convert(branch(fix(var('left')),fix(var('right'))),zz))
                elif ns:
                    eq=use(unequal_laws[label],[target,var('key')],[{'Hypothesis':index}]);middle=trans(convert(body,normal(body,objects)),lifted(eq,replace(normal(body,objects),binary('==',target,var('key')),var('prune_hole'))),convert(replace(normal(body,objects),binary('==',target,var('key')),{'Bool':False}),zz))
                else:middle=convert(body,zz)
                false_case=trans(convert(aa,n),lifted({'Hypothesis':index},replace(n,normal(g,objects),var('prune_hole'))),convert(replace(n,normal(g,objects),{'Bool':False}),zz))
                ps.append((ns,{'BoolSplit':dict(condition=g,**{'from':aa,'to':zz},on_false=false_case,on_true=trans(first,middle))}))
            unchanged[label]=induction(operation+'_'+label+'_unchanged',[['tree',T],*rest],a,z,ps)
        a,z=choice(outside(var('tree')),fix(var('tree')),update(fix(var('tree')))),update(fix(var('tree')))
        def drop_update_branch(lo,hi):
            current=normal(a,objects);proof=convert(a,current)
            for x,y,index in [(normal(low(var('tree')),objects),{'Bool':lo},0),(normal(high(var('tree')),objects),{'Bool':hi},1)]:
                updated=replace(current,x,y);proof=trans(proof,lifted({'Hypothesis':index},replace(current,x,var('prune_hole'))),convert(updated,normal(updated,objects)));current=normal(updated,objects)
            if not lo and not hi:return trans(proof,convert(current,z))
            label='low' if lo else 'high';g=low(var('tree')) if lo else high(var('tree'));eq={'Hypothesis':0 if lo else 1};old=fix(var('tree'))
            pruning=trans(convert(z,choice({'Bool':True},z,old)),{'Sym':lifted(eq,choice(var('prune_hole'),z,old))},use(unchanged[label],[var('tree'),*args]))
            return trans(proof,{'Sym':pruning})
        branches={}
        for lo in [False,True]:branches['on_true' if lo else 'on_false']={'BoolSplit':dict(condition=high(var('tree')),**{'from':a,'to':z},on_false=drop_update_branch(lo,False),on_true=drop_update_branch(lo,True))}
        drop=law(operation+'_drop_pruning',[['tree',T],*rest],a,z,{'BoolSplit':dict(condition=low(var('tree')),**{'from':a,'to':z},**branches)})
        changed=empty if operation=='remove' else leaf(var('key'),new);leafbody=choice(binary('==',target,var('key')),changed,leaf(var('key'),var('row')))
        fastop=fun(operation,[['tree',T],*rest],T,choice(raw_outside(var('tree')),var('tree'),match(var('tree'),[([],empty),(['key','row'],leafbody),(bindings,branch({'SelfCall':[var('left'),*args]},{'SelfCall':[var('right'),*args]}))])),0)
        fast=lambda t:call(fastop,[t,*args]);a,z=fast(fix(var('tree'))),update(fix(var('tree')));ps=[]
        for ns,t in treecases:
            aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t);intermediate=choice(outside(t),fix(t),update(fix(t)))
            hypotheses=[(fast(fix(var('left'))),update(fix(var('left')))),(fast(fix(var('right'))),update(fix(var('right'))))] if len(ns)>2 else ()
            ps.append((ns,trans(derive(aa,intermediate,objects,hypotheses),use(drop,[t,*args]))))
        equivalent=induction('indexed_'+operation+'_equivalent',[['tree',T],*rest],a,z,ps)
        source_op=lambda t:call(table[operation],[t,*args]);a,z=logical(fast(fix(var('tree')))),source_op(logical(var('tree')))
        proof=trans({'Call':dict(function=decode,arguments=[use(equivalent,[var('tree'),*args])])},use(names[operation+'_preserves_rows'],[fix(var('tree')),*args]),{'Call':dict(function=table[operation],arguments=[use(names['repair_preserves_rows'],[var('tree')]),*({'Refl':x} for x in args)])})
        law('indexed_'+operation+'_preserves_rows',[['tree',T],*rest],a,z,proof)
        a,z=fix(fast(fix(var('tree')))),fast(fix(var('tree')))
        proof=trans({'Call':dict(function=repair,arguments=[use(equivalent,[var('tree'),*args])])},use(commute,[fix(var('tree')),*args]),{'Call':dict(function=rawop,arguments=[use(names['repair_idempotent'],[var('tree')]),*({'Refl':x} for x in args)])},{'Sym':use(equivalent,[var('tree'),*args])})
        law('indexed_'+operation+'_preserves_metadata',[['tree',T],*rest],a,z,proof)
    cond=var('condition');aa,bb=var('a'),var('b')
    x,y=logical(choice(cond,aa,bb)),choice(cond,logical(aa),logical(bb))
    distribute=law('decode_choice',[['condition','Bool'],['a',T],['b',T]],x,y,{'BoolCases':dict(variable='condition',**{'from':x,'to':y},**{k:convert(replace(x,cond,{'Bool':b}),replace(y,cond,{'Bool':b})) for k,b in [('on_false',False),('on_true',True)]})})
    l,r=var('left'),var('right');x,y=logical(branch(l,r)),cat(logical(l),logical(r))
    decode_branch=law('decode_branch',[['left',T],['right',T]],x,y,convert(x,y))
    cond=var('condition');value=var('value');x,y=choice(cond,value,value),value
    same_rows=law('same_rows_choice',[['condition','Bool'],['value',R]],x,y,{'BoolCases':dict(variable='condition',**{'from':x,'to':y},on_false=convert(value,value),on_true=convert(value,value))})
    # Database-owned AVL sequence rotations. Rotations retain enumeration order.
    # These definitions are emitted literally by every lowering.
    a,z=cat(var('left'),nil),var('left')
    append_nil=induction('append_right_identity',[['left',R]],a,z,[([],convert(cat(nil,nil),nil)),(['key','row','tail'],derive(replace(a,var('left'),boundrows),boundrows,objects,[(cat(var('tail'),nil),var('tail'))]))])
    def canonical_rows(t):
        n=normal(t,objects);start=convert(t,n)
        if 'Construct' in n and n['Construct']['datatype']==rows:
            c=n['Construct'];children=[canonical_rows(x) if j==2 else (x,{'Refl':x}) for j,x in enumerate(c['arguments'])]
            result=cons(rows,c['constructor'],[x for x,p in children]);p={'Construct':dict(datatype=rows,constructor=c['constructor'],arguments=[p for x,p in children])}
            return result,trans(start,p)
        if n.get('Call',{}).get('function')==append:
            l,r=n['Call']['arguments'];l,pl=canonical_rows(l);r,pr=canonical_rows(r);p=trans(start,{'Call':dict(function=append,arguments=[pl,pr])});current=cat(l,r)
            if r==nil:return l,trans(p,use(append_nil,[l]))
            if l.get('Call',{}).get('function')==append:
                x,y=l['Call']['arguments'];following=cat(x,cat(y,r));end,q=canonical_rows(following)
                return end,trans(p,use(names['append_associative'],[x,y,r]),q)
            result=normal(current,objects)
            if result!=current:
                end,q=canonical_rows(result);return end,trans(p,convert(current,result),q)
            return current,p
        return n,start
    def row_equality(a,z):
        aa,pa=canonical_rows(a);zz,pz=canonical_rows(z)
        if aa!=zz:raise ValueError('rotation changed enumeration '+str((aa,zz))[:1000])
        return trans(pa,convert(aa,zz),{'Sym':pz})
    def flatten_branch(t):
        if t.get('Call',{}).get('function')==smart:
            l,r=t['Call']['arguments'];ll,pl=flatten_branch(l);rr,pr=flatten_branch(r)
            return cat(ll,rr),trans(use(decode_branch,[l,r]),{'Call':dict(function=append,arguments=[pl,pr])})
        return logical(t),{'Refl':logical(t)}
    def flattened_rows(t,z):
        a,p=flatten_branch(t);return trans(p,row_equality(a,z))
    def logical_choice(goal,end,guard,one,two,pone,ptwo):
        return trans(convert(goal,logical(choice(guard,one,two))),use(distribute,[guard,one,two]),lifted(pone,choice(guard,var('prune_hole'),logical(two))),lifted(ptwo,choice(guard,end,var('prune_hole'))),use(same_rows,[guard,end]))
    def rotation(label):
        aa,bb,cc=map(var,['a','b','c']);middle_bindings=['rot_left','rot_right','rot_lo','rot_hi','rot_sum','rot_count','rot_height']
        single=branch(aa,branch(bb,cc)) if label=='left' else branch(branch(aa,bb),cc)
        double=branch(branch(aa,var('rot_left')),branch(var('rot_right'),cc))
        guard=binary('<',field('height',aa if label=='left' else cc),field('height',bb))
        f=fun('rotate_'+label,[['a',T],['b',T],['c',T]],T,choice(guard,match(bb,[([],single),(['rot_key','rot_row'],single),(middle_bindings,double)]),single))
        goal=logical(call(f,[aa,bb,cc]));end=cat(logical(aa),cat(logical(bb),logical(cc)));ps=[]
        for ns,t in [([],empty),(['rot_key','rot_row'],leaf(var('rot_key'),var('rot_row'))),(middle_bindings,node(*map(var,middle_bindings)))]:
            ss=replace(single,bb,t);dd=double if len(ns)>2 else ss;g=replace(guard,bb,t);x,z=replace(goal,bb,t),replace(end,bb,t)
            ps.append((ns,logical_choice(x,z,g,dd,ss,flattened_rows(dd,z),flattened_rows(ss,z))))
        p=induction('rotate_'+label+'_preserves_rows',[['b',T],['a',T],['c',T]],goal,end,ps)
        return f,p
    rotate_l,rotate_l_law=rotation('left');rotate_r,rotate_r_law=rotation('right')
    heavy=lambda l,r:binary('>',field('height',l),binary('+',field('height',r),{'U64':1}))
    def one_side(label,rotate,rotate_law):
        l,r=map(var,['left','right']);which=l if label=='left' else r
        bs=['side_left','side_right','side_lo','side_hi','side_sum','side_count','side_height'];args=[var('side_left'),var('side_right'),r] if label=='left' else [l,var('side_left'),var('side_right')];chosen=call(rotate,args)
        guard=heavy(l,r) if label=='left' else heavy(r,l)
        f=fun('balance_'+label,[['left',T],['right',T]],T,choice(guard,match(which,[([],branch(l,r)),(['side_key','side_row'],branch(l,r)),(bs,chosen)]),branch(l,r)))
        goal=logical(call(f,[l,r]));end=cat(logical(l),logical(r));ps=[]
        for ns,t in [([],empty),(['side_key','side_row'],leaf(var('side_key'),var('side_row'))),(bs,node(*map(var,bs)))]:
            single=replace(branch(l,r),which,t);double=chosen if len(ns)>2 else single;x,z=replace(goal,which,t),replace(end,which,t);g=replace(guard,which,t)
            if len(ns)>2:
                rotation_end=cat(logical(args[0]),cat(logical(args[1]),logical(args[2])));pdouble=trans(use(rotate_law,[args[1],args[0],args[2]]),row_equality(rotation_end,z))
            else:pdouble=flattened_rows(single,z)
            ps.append((ns,logical_choice(x,z,g,double,single,pdouble,flattened_rows(single,z))))
        p=induction('balance_'+label+'_preserves_rows',[[which['Var'],T],[('right' if label=='left' else 'left'),T]],goal,end,ps)
        return f,p
    balance_l,balance_l_law=one_side('left',rotate_l,rotate_l_law);balance_r,balance_r_law=one_side('right',rotate_r,rotate_r_law)
    l,r=map(var,['left','right']);bal=fun('balance',[['left',T],['right',T]],T,choice(heavy(l,r),call(balance_l,[l,r]),call(balance_r,[l,r])))
    balanced=lambda l,r:call(bal,[l,r]);goal=logical(balanced(l,r));end=cat(logical(l),logical(r))
    rules=[(logical(call(f,[l,r])),end,use(p,[l,r] if f==balance_l else [r,l])) for f,p in [(balance_l,balance_l_law),(balance_r,balance_r_law)]]
    leftterm=call(balance_l,[l,r]);rightterm=call(balance_r,[l,r]);condition=heavy(l,r)
    middle=choice(condition,logical(leftterm),logical(rightterm))
    p=trans(convert(goal,logical(choice(condition,leftterm,rightterm))),use(distribute,[condition,leftterm,rightterm]),lifted(use(balance_l_law,[l,r]),choice(condition,var('prune_hole'),logical(rightterm))),lifted(use(balance_r_law,[r,l]),choice(condition,end,var('prune_hole'))),derive(choice(condition,end,end),end,objects))
    law('balance_preserves_rows',[['left',T],['right',T]],goal,end,p)
    # The maximum routes insertion to the first subtree containing a greater key.
    # If none exists on the left, the original logical insertion scans the right.
    greater_rows=fun('greater_rows',[['rows',R],['target','U64']],'Bool',match(var('rows'),[([],{'Bool':False}),(['key','row','tail'],choice(binary('<',target,var('key')),{'Bool':True},{'SelfCall':[var('tail'),target]}))]),0)
    greater_tree=fun('greater_tree',[['tree',T],['target','U64']],'Bool',match(var('tree'),[([],{'Bool':False}),(['key','row'],binary('<',target,var('key'))),(bindings,choice({'SelfCall':[var('left'),target]},{'Bool':True},{'SelfCall':[var('right'),target]}))]),0)
    gr=lambda r:call(greater_rows,[r,target]);gt=lambda t:call(greater_tree,[t,target]);boolean_or=lambda a,b:choice(a,{'Bool':True},b)
    x,y,w=map(var,['x','a','b']);maxlaw=scalar('below_maximum',[['x','U64'],['a','U64'],['b','U64']],binary('<',x,maximum(y,w)),boolean_or(binary('<',x,y),binary('<',x,w)))
    a,z=binary('<',target,field('high',fix(var('tree')))),gt(var('tree'));ps=[]
    for ns,t in treecases:
        aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t)
        if len(ns)>2:
            start=binary('<',target,maximum(field('high',fix(var('left'))),field('high',fix(var('right')))))
            intermediate=boolean_or(binary('<',target,field('high',fix(var('left')))),binary('<',target,field('high',fix(var('right')))))
            q=use(maxlaw,[target,field('high',fix(var('left'))),field('high',fix(var('right')))])
            p=trans(convert(aa,start),q,derive(intermediate,zz,objects,[(binary('<',target,field('high',fix(var('left')))),gt(var('left'))),(binary('<',target,field('high',fix(var('right')))),gt(var('right')))]))
        elif ns:p=convert(aa,zz)
        else:p=derive(aa,zz,objects,leaf=lambda a,z:use(scalar('below_zero',[['target','U64']],binary('<',target,{'U64':0}),{'Bool':False}),[target]))
        ps.append((ns,p))
    max_tree=induction('maximum_detects_greater',[['tree',T],['target','U64']],a,z,ps)
    a,z=gr(cat(var('left'),var('right'))),boolean_or(gr(var('left')),gr(var('right')))
    greater_append=induction('greater_append',[['left',R],['right',R],['target','U64']],a,z,[([],convert(replace(a,var('left'),nil),replace(z,var('left'),nil))),(['key','row','tail'],derive(replace(a,var('left'),boundrows),replace(z,var('left'),boundrows),objects,[(replace(a,var('left'),var('tail')),replace(z,var('left'),var('tail')))]))])
    a,z=gt(var('tree')),gr(logical(var('tree')))
    rule=(gr(cat(logical(var('left')),logical(var('right')))),boolean_or(gr(logical(var('left'))),gr(logical(var('right')))),use(greater_append,[logical(var('left')),logical(var('right')),target]))
    greater_logical=induction('greater_preserves_rows',[['tree',T],['target','U64']],a,z,[(ns,derive(replace(a,var('tree'),t),replace(z,var('tree'),t),objects,[(gt(var('left')),gr(logical(var('left')))),(gt(var('right')),gr(logical(var('right'))))] if len(ns)>2 else (),rules=[rule] if len(ns)>2 else ())) for ns,t in treecases])
    max_logical=law('maximum_matches_rows',[['tree',T],['target','U64']],binary('<',target,field('high',fix(var('tree')))),gr(logical(var('tree'))),trans(use(max_tree,[var('tree'),target]),use(greater_logical,[var('tree'),target])))
    insert=lambda r:call(table['insert'],[r,target,new]);a,z=insert(cat(var('left'),var('right'))),choice(gr(var('left')),cat(insert(var('left')),var('right')),cat(var('left'),insert(var('right'))))
    insert_append=induction('insert_append',[['left',R],['right',R],['target','U64'],['new',row]],a,z,[([],convert(replace(a,var('left'),nil),replace(z,var('left'),nil))),(['key','row','tail'],derive(replace(a,var('left'),boundrows),replace(z,var('left'),boundrows),objects,[(replace(a,var('left'),var('tail')),replace(z,var('left'),var('tail')))]))])
    insert_tree=fun('insert',[['tree',T],['target','U64'],['new',row]],T,match(var('tree'),[([],leaf(target,new)),(['key','row'],choice(binary('<',target,var('key')),balanced(leaf(target,new),leaf(var('key'),var('row'))),balanced(leaf(var('key'),var('row')),leaf(target,new)))),(bindings,choice(binary('<',target,field('high',var('left'))),balanced({'SelfCall':[var('left'),target,new]},var('right')),balanced(var('left'),{'SelfCall':[var('right'),target,new]})))]),0)
    fast_insert=lambda t:call(insert_tree,[t,target,new]);a,z=logical(fast_insert(fix(var('tree')))),insert(logical(var('tree')));ps=[]
    for ns,t in treecases:
        aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t)
        if not ns:p=convert(aa,zz)
        else:
            if len(ns)==2:
                l,r=leaf(target,new),leaf(var('key'),var('row'));guard=binary('<',target,var('key'));one,two=balanced(l,r),balanced(r,l);first,second=cat(logical(l),logical(r)),cat(logical(r),logical(l))
                p1=use(names['balance_preserves_rows'],[l,r]);p2=use(names['balance_preserves_rows'],[r,l]);following=choice(guard,first,second);finish=derive(following,zz,objects)
            else:
                l,r=fix(var('left')),fix(var('right'));il,ir=fast_insert(l),fast_insert(r);guard=binary('<',target,field('high',l));one,two=balanced(il,r),balanced(l,ir)
                first,second=cat(insert(logical(var('left'))),logical(var('right'))),cat(logical(var('left')),insert(logical(var('right'))))
                p1=trans(use(names['balance_preserves_rows'],[il,r]),{'Call':dict(function=append,arguments=[{'Hypothesis':0},use(names['repair_preserves_rows'],[var('right')])])})
                p2=trans(use(names['balance_preserves_rows'],[l,ir]),{'Call':dict(function=append,arguments=[use(names['repair_preserves_rows'],[var('left')]),{'Hypothesis':1}])})
                following=choice(guard,first,second);replaced_guard=gr(logical(var('left')));finish=trans(lifted(use(max_logical,[var('left'),target]),choice(var('prune_hole'),first,second)),{'Sym':use(insert_append,[logical(var('left')),logical(var('right')),target,new])},convert(insert(cat(logical(var('left')),logical(var('right')))),zz))
            p=trans(convert(aa,logical(choice(guard,one,two))),use(distribute,[guard,one,two]),lifted(p1,choice(guard,var('prune_hole'),logical(two))),lifted(p2,choice(guard,first,var('prune_hole'))),finish)
        ps.append((ns,p))
    insertion=induction('indexed_insert_preserves_rows',[['tree',T],['target','U64'],['new',row]],a,z,ps)
    # Factored congruence avoids repeatedly normalising every cached field.
    l,r=var('left'),var('right');a,z=fix(branch(l,r)),branch(l,r)
    branch_valid=law('branch_preserves_metadata',[['left',T],['right',T]],a,z,trans(convert(a,branch(fix(l),fix(r))),{'Call':dict(function=smart,arguments=[{'Hypothesis':0},{'Hypothesis':1}])}),[{'from':fix(l),'to':l},{'from':fix(r),'to':r}])
    cond=var('condition');l,r=var('a'),var('b');a,z=fix(choice(cond,l,r)),choice(cond,fix(l),fix(r))
    repair_choice=law('repair_choice',[['condition','Bool'],['a',T],['b',T]],a,z,{'BoolCases':dict(variable='condition',**{'from':a,'to':z},**{k:convert(replace(a,cond,{'Bool':b}),replace(z,cond,{'Bool':b})) for k,b in [('on_false',False),('on_true',True)]})})
    # A generic choice and smart-node validity lemma keeps rotation proofs small.
    cond=var('condition');l,r=var('a'),var('b');a,z=fix(choice(cond,l,r)),choice(cond,l,r)
    choice_valid=law('choice_preserves_metadata',[['condition','Bool'],['a',T],['b',T]],a,z,trans(use(repair_choice,[cond,l,r]),lifted({'Hypothesis':0},choice(cond,var('prune_hole'),fix(r))),lifted({'Hypothesis':1},choice(cond,l,var('prune_hole')))),[{'from':fix(l),'to':l},{'from':fix(r),'to':r}])
    def valid_choice(guard,one,two,pone,ptwo):
        return trans(use(repair_choice,[guard,one,two]),lifted(pone,choice(guard,var('prune_hole'),fix(two))),lifted(ptwo,choice(guard,one,var('prune_hole'))))
    def node_valid(l,r,pl,pr):return use(branch_valid,[l,r],[pl,pr])
    idem=lambda t:use(names['repair_idempotent'],[t])
    rotation_valid={}
    for label,f in [('left',rotate_l),('right',rotate_r)]:
        aa,bb,cc=map(var,['a','b','c']);goal=fix(call(f,[aa,fix(bb),cc]));end=call(f,[aa,fix(bb),cc]);ps=[]
        nsnode=['valid_left','valid_right','valid_lo','valid_hi','valid_sum','valid_count','valid_height']
        for ns,t in [([],empty),(['valid_key','valid_row'],leaf(var('valid_key'),var('valid_row'))),(nsnode,node(*map(var,nsnode)))]:
            middle=fix(t);pm=use(names['repair_idempotent'],[t]);pa,pc={'Hypothesis':0},{'Hypothesis':1}
            single=branch(aa,branch(middle,cc)) if label=='left' else branch(branch(aa,middle),cc)
            p_single=node_valid(aa,branch(middle,cc),pa,node_valid(middle,cc,pm,pc)) if label=='left' else node_valid(branch(aa,middle),cc,node_valid(aa,middle,pa,pm),pc)
            if len(ns)>2:
                ml,mr=fix(var('valid_left')),fix(var('valid_right'));double=branch(branch(aa,ml),branch(mr,cc));p_double=node_valid(branch(aa,ml),branch(mr,cc),node_valid(aa,ml,pa,idem(var('valid_left'))),node_valid(mr,cc,idem(var('valid_right')),pc))
            else:double,p_double=single,p_single
            guard=binary('<',field('height',aa if label=='left' else cc),field('height',middle))
            x,y=replace(goal,bb,t),replace(end,bb,t);p=trans(convert(x,fix(choice(guard,double,single))),valid_choice(guard,double,single,p_double,p_single),convert(choice(guard,double,single),y))
            sorts=[] if not ns else ['U64',row] if len(ns)==2 else [T,T,'U64','U64',sum_sort,count_sort,'U64']
            params=[*zip(ns,sorts),['a',T],['c',T]];conds=[{'from':fix(aa),'to':aa},{'from':fix(cc),'to':cc}]
            lemma=law(None,params,x,y,p,conds);ps.append((ns,use(lemma,[var(n) for n,_ in params],[pa,pc])))
        rotation_valid[label]=induction('rotate_'+label+'_preserves_metadata',[['b',T],['a',T],['c',T]],goal,end,ps,[{'from':fix(aa),'to':aa},{'from':fix(cc),'to':cc}])
    side_valid={}
    for label,f,rotate in [('left',balance_l,rotate_l),('right',balance_r,rotate_r)]:
        l,r=map(var,['left','right']);fl,fr=fix(l),fix(r);which=l if label=='left' else r
        goal=fix(call(f,[fl,fr]));end=call(f,[fl,fr]);ps=[];nsnode=['valid_left','valid_right','valid_lo','valid_hi','valid_sum','valid_count','valid_height']
        for ns,t in [([],empty),(['valid_key','valid_row'],leaf(var('valid_key'),var('valid_row'))),(nsnode,node(*map(var,nsnode)))]:
            ll,rr=replace(fl,which,t),replace(fr,which,t);single=branch(ll,rr);p_single=node_valid(ll,rr,idem(t if label=='left' else l),idem(r if label=='left' else t))
            if len(ns)>2:
                al,ar=fix(var('valid_left')),fix(var('valid_right'));args=[al,ar,rr] if label=='left' else [ll,al,ar];double=call(rotate,args)
                rawmiddle=var('valid_right' if label=='left' else 'valid_left');p_double=use(rotation_valid[label],[rawmiddle,args[0],args[2]],[idem(var('valid_left') if label=='left' else l),idem(r if label=='left' else var('valid_right'))])
            else:double,p_double=single,p_single
            guard=heavy(ll,rr) if label=='left' else heavy(rr,ll);x,y=replace(goal,which,t),replace(end,which,t)
            p=trans(convert(x,fix(choice(guard,double,single))),valid_choice(guard,double,single,p_double,p_single),convert(choice(guard,double,single),y))
            sorts=[] if not ns else ['U64',row] if len(ns)==2 else [T,T,'U64','U64',sum_sort,count_sort,'U64']
            params=[*zip(ns,sorts),[('right' if label=='left' else 'left'),T]];lemma=law(None,params,x,y,p);ps.append((ns,use(lemma,[var(n) for n,_ in params])))
        side_valid[label]=induction('balance_'+label+'_preserves_metadata',[[which['Var'],T],[('right' if label=='left' else 'left'),T]],goal,end,ps)
    l,r=map(var,['left','right']);fl,fr=fix(l),fix(r);one,two=call(balance_l,[fl,fr]),call(balance_r,[fl,fr]);guard=heavy(fl,fr)
    a,z=fix(balanced(fl,fr)),balanced(fl,fr);valid_balanced=law('balance_repaired',[['left',T],['right',T]],a,z,trans(convert(a,fix(choice(guard,one,two))),valid_choice(guard,one,two,use(side_valid['left'],[l,r]),use(side_valid['right'],[r,l])),convert(choice(guard,one,two),z)))
    a,z=fix(balanced(l,r)),balanced(l,r);conditions=[{'from':fix(l),'to':l},{'from':fix(r),'to':r}];lift_inputs={'Call':dict(function=bal,arguments=[{'Hypothesis':0},{'Hypothesis':1}])}
    balance_valid=law('balance_preserves_metadata',[['left',T],['right',T]],a,z,trans({'Sym':{'Call':dict(function=repair,arguments=[lift_inputs])}},use(valid_balanced,[l,r]),lift_inputs),conditions)
    a,z=fix(fast_insert(fix(var('tree')))),fast_insert(fix(var('tree')));ps=[]
    for ns,t in treecases:
        aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t)
        if not ns:p=convert(aa,zz)
        else:
            if len(ns)==2:
                l,r=leaf(target,new),leaf(var('key'),var('row'));guard=binary('<',target,var('key'));one,two=balanced(l,r),balanced(r,l)
                p1=use(balance_valid,[l,r],[convert(fix(l),l),convert(fix(r),r)]);p2=use(balance_valid,[r,l],[convert(fix(r),r),convert(fix(l),l)])
            else:
                l,r=fix(var('left')),fix(var('right'));il,ir=fast_insert(l),fast_insert(r);guard=binary('<',target,field('high',l));one,two=balanced(il,r),balanced(l,ir)
                p1=use(balance_valid,[il,r],[{'Hypothesis':0},use(names['repair_idempotent'],[var('right')])]);p2=use(balance_valid,[l,ir],[use(names['repair_idempotent'],[var('left')]),{'Hypothesis':1}])
            p=trans(convert(aa,fix(choice(guard,one,two))),use(repair_choice,[guard,one,two]),lifted(p1,choice(guard,var('prune_hole'),fix(two))),lifted(p2,choice(guard,one,var('prune_hole'))),convert(choice(guard,one,two),zz))
        sorts=[] if not ns else ['U64',row] if len(ns)==2 else [T,T,'U64','U64',sum_sort,count_sort,'U64']
        params=[*zip(ns,sorts),['target','U64'],['new',row]]
        conditions=[{'from':fix(fast_insert(fix(var(n)))),'to':fast_insert(fix(var(n)))} for n in ['left','right']] if len(ns)>2 else []
        lemma=law(None,params,aa,zz,p,conditions)
        ps.append((ns,use(lemma,[var(n) for n,_ in params],[{'Hypothesis':j} for j in range(len(conditions))])))
    induction('indexed_insert_preserves_metadata',[['tree',T],['target','U64'],['new',row]],a,z,ps)
    # Initial encoding builds a balanced ordered sequence without assuming sorted
    # keys or uniqueness. Prepending preserves the complete logical enumeration.
    k,v=var('prepend_key'),var('prepend_value');prepend=fun('prepend',[['tree',T],['prepend_key','U64'],['prepend_value',row]],T,match(var('tree'),[([],leaf(k,v)),(['old_key','old_row'],balanced(leaf(k,v),leaf(var('old_key'),var('old_row')))),(bindings,balanced({'SelfCall':[var('left'),k,v]},var('right')))]),0)
    prep=lambda t:call(prepend,[t,k,v]);prefix=lambda r:cons(rows,1,[k,v,r]);a,z=logical(prep(fix(var('tree')))),prefix(logical(var('tree')));ps=[]
    for ns,t in treecases:
        aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t)
        if not ns:p=convert(aa,zz)
        else:
            l,r=(leaf(k,v),leaf(var('key'),var('row'))) if len(ns)==2 else (prep(fix(var('left'))),fix(var('right')))
            p=trans(convert(aa,logical(balanced(l,r))),use(names['balance_preserves_rows'],[l,r]))
            if len(ns)>2:p=trans(p,{'Call':dict(function=append,arguments=[{'Hypothesis':0},use(names['repair_preserves_rows'],[var('right')])])})
            p=trans(p,convert(cat(logical(l),logical(r)) if len(ns)==2 else cat(prefix(logical(var('left'))),logical(var('right'))),zz))
        ps.append((ns,p))
    prepend_rows=induction('prepend_preserves_rows',[['tree',T],['prepend_key','U64'],['prepend_value',row]],a,z,ps)
    a,z=fix(prep(fix(var('tree')))),prep(fix(var('tree')));ps=[]
    for ns,t in treecases:
        aa,zz=replace(a,var('tree'),t),replace(z,var('tree'),t)
        if not ns:p=convert(aa,zz)
        else:
            l,r=(leaf(k,v),leaf(var('key'),var('row'))) if len(ns)==2 else (prep(fix(var('left'))),fix(var('right')))
            pl,pr=(convert(fix(l),l),convert(fix(r),r)) if len(ns)==2 else ({'Hypothesis':0},idem(var('right')))
            p=trans(convert(aa,fix(balanced(l,r))),use(balance_valid,[l,r],[pl,pr]),convert(balanced(l,r),zz))
        ps.append((ns,p))
    prepend_valid=induction('prepend_preserves_metadata',[['tree',T],['prepend_key','U64'],['prepend_value',row]],a,z,ps)
    encode=fun('encode_rows',[['rows',R]],T,match(var('rows'),[([],empty),(['encode_key','encode_value','encode_tail'],call(prepend,[{'SelfCall':[var('encode_tail')]},var('encode_key'),var('encode_value')]))]),0)
    enc=lambda r:call(encode,[r]);a,z=logical(enc(var('rows'))),var('rows');encoded=enc(var('encode_tail'));ek,ev=var('encode_key'),var('encode_value');b=cons(rows,1,[ek,ev,var('encode_tail')])
    # Both encoding facts are factored: the row theorem may use the previously
    # proved metadata theorem when replacing a repaired encoded child.
    a,z=fix(enc(var('rows'))),enc(var('rows'))
    child=enc(var('encode_tail'));pn=call(prepend,[child,ek,ev]);p=trans({'Sym':{'Call':dict(function=repair,arguments=[{'Call':dict(function=prepend,arguments=[{'Hypothesis':0},{'Refl':ek},{'Refl':ev}])}])}},use(prepend_valid,[child,ek,ev]),{'Call':dict(function=prepend,arguments=[{'Hypothesis':0},{'Refl':ek},{'Refl':ev}])})
    encode_valid=induction('encode_preserves_metadata',[['rows',R]],a,z,[([],convert(fix(enc(nil)),enc(nil))),(['encode_key','encode_value','encode_tail'],trans(convert(replace(a,var('rows'),b),fix(pn)),p,convert(pn,replace(z,var('rows'),b))))])
    a,z=logical(enc(var('rows'))),var('rows');p=trans({'Sym':{'Call':dict(function=decode,arguments=[{'Call':dict(function=prepend,arguments=[use(encode_valid,[var('encode_tail')]),{'Refl':ek},{'Refl':ev}])}])}},use(prepend_rows,[child,ek,ev]),{'Construct':dict(datatype=rows,constructor=1,arguments=[{'Refl':ek},{'Refl':ev},{'Hypothesis':0}])})
    induction('encode_preserves_rows',[['rows',R]],a,z,[([],convert(logical(enc(nil)),nil)),(['encode_key','encode_value','encode_tail'],trans(convert(replace(a,var('rows'),b),logical(pn)),p))])
    # A checked flattening identity does not yet grant range pruning authority.
    # Those obligations are produced separately from metadata validity.
    if layout_only:
        names['_aggregates']=aggregates
    else:
        from producers.indexed_representation import proposal
        proposal(model,objects,names,add,fun,law)
    return objects,names

def publish_checked(staged,root,compiler,source,report):
    """Publish only after exact source admission; preserve the compact view pin."""
    import shutil
    from ink_knowledge.store import read,immutable
    staged=Path(staged);root=Path(root);compiler=Path(compiler).resolve()
    request=staged/'request.json';raw=request.read_bytes()
    if len(raw)>16_000_000:raise ValueError('representation request byte limit')
    checked=subprocess.run([str(compiler),'check-representation',str(Path(source).resolve()),str(request.resolve())],capture_output=True,text=True,check=True)
    receipt=json.loads(checked.stdout);proposal=json.loads(raw)
    if receipt.get('status')!='checked' or receipt.get('representation')!=proposal['representation'] or receipt.get('source')!=proposal['input_core_sha256']:raise ValueError('admission receipt mismatch')
    old=Store(root);candidate=Store(staged);previous=old.snapshot_id
    objects={i:old.object(i) for i in old.members()}
    objects.update({i:candidate.object(i) for i in candidate.members()})
    names=read(root/'store/names.json');names.update(read(staged/'store/names.json'))
    admitted=Store.publish(root,objects.values(),names)
    # Immutable compact snapshots are ordinary database history. They keep
    # authenticated views below the existing request bound as the catalog grows.
    for directory in ['trees','snapshots']:
        for path in (staged/'store'/directory).glob('*.json'):
            immutable(root/'store'/directory/path.name,read(path))
    pin=root/'store/snapshots'/f'{candidate.snapshot_id}.json'
    pinned=Store(root,snapshot=pin)
    if canonical(pinned.bundle([proposal['representation']]))!=canonical(proposal['knowledge']):raise ValueError('published pin differs from checked view')
    admitted.rebuild()
    result=dict(status='checked',source=receipt['source'],representation=receipt['representation'],previous_snapshot=previous,snapshot=admitted.snapshot_id,view_snapshot=candidate.snapshot_id,request_sha256=hashlib.sha256(raw).hexdigest(),obligations=len(receipt['obligations']),entries=read(staged/'store/names.json'))
    Path(report).parent.mkdir(parents=True,exist_ok=True);Path(report).write_bytes(canonical(result)+b'\n')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('model',type=Path);p.add_argument('-o','--output',type=Path,required=True)
    p.add_argument('--publish-root',type=Path);p.add_argument('--compiler',type=Path);p.add_argument('--source',type=Path);p.add_argument('--report',type=Path)
    a=p.parse_args();objects,names=definitions(json.loads(a.model.read_text()))
    store=Store.publish(a.output,objects.values(),{'indexed-aggregate/'+k:v for k,v in names.items()},leaf_size=2)
    (a.output/'view.json').write_bytes(canonical(store.bundle(list(names.values())))+b'\n')
    (a.output/'request.json').write_bytes(canonical(dict(schema=1,semantics='ink-source-representation-v1',input_core_sha256=json.loads(a.model.read_text())['source'],knowledge=store.bundle([names['representation']]),representation=names['representation']))+b'\n')
    if a.publish_root:
        if not all([a.compiler,a.source,a.report]):p.error('publication requires --compiler, --source and --report')
        print(json.dumps(publish_checked(a.output,a.publish_root,a.compiler,a.source,a.report)))
    else:print(json.dumps(dict(status='proposed',definitions=names,snapshot=store.snapshot_id)))
