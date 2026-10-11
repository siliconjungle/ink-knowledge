"""Author ordinary universal laws for a row-parametric ordered sequence tree."""
from action_replacement import var,call,cons
from sequence_tree import D

def prove(names,objects,add,row_sort):
    table,option=names['table'],names['option']
    from tree_proofs import Tactic
    tactic=Tactic(objects,add)
    tactic.blocked.update(names[n]for n in ['minimum','maximum','height','measure'])
    f=lambda name,*xs:call(names[name],list(xs))
    x,y,z=map(var,['xs','ys','zs']);l,r,t=map(var,['left','right','tree'])
    nil=cons(table,0,[])
    names['append-empty']=tactic.theorem('append-empty',[['xs',D(table)]],f('append',x,nil),x,'xs')
    names['append-associative']=tactic.theorem('append-associative',[['xs',D(table)],['ys',D(table)],['zs',D(table)]],
        f('append',f('append',x,y),z),f('append',x,f('append',y,z)),'xs')
    flatten=lambda t:f('decode',t)
    pair=lambda l,r:f('append',flatten(l),flatten(r))
    names['node-order']=tactic.theorem('node-order',[['left',D(names['datatype'])],['right',D(names['datatype'])]],flatten(f('node',l,r)),pair(l,r))
    tactic.cases_first=False
    names['balance-order']=tactic.theorem('balance-order',[['left',D(names['datatype'])],['right',D(names['datatype'])]],flatten(f('balance',l,r)),pair(l,r))
    names['join-right-order']=tactic.theorem('join-right-order',[['left',D(names['datatype'])],['right',D(names['datatype'])]],flatten(f('join_right',l,r)),pair(l,r),'right',['left'])
    names['join-order']=tactic.theorem('join-order',[['left',D(names['datatype'])],['right',D(names['datatype'])]],flatten(f('join',l,r)),pair(l,r),'left',['right'])
    names['roundtrip']=tactic.theorem('roundtrip',[['xs',D(table)]],flatten(f('encode',x)),x,'xs')
    from scalar_tactic import Scalar
    from point_delta import binary
    tactic.scalar=Scalar(add,tactic.sort,tactic.normal)
    tactic.blocked.discard(names['node'])
    tactic.cases_first=True
    tactic.eager.update(names[n]for n in ['minimum','maximum','height','measure'])
    valid=lambda t:f('valid',t)
    tactic.transparent.add(names['valid'])
    params=[['left',D(names['datatype'])],['right',D(names['datatype'])]]
    for component in ['minimum_valid','maximum_valid','measure_valid']:
        check=lambda t:f(component,t)
        guard=binary('&&',check(l),check(r))
        tactic.blocked.discard(names['node']);tactic.blocked.discard(names['balance'])
        tactic.cases_first=True
        names['node-'+component]=tactic.theorem('node-'+component,params,check(f('node',l,r)),{'Bool':True},guard=guard)
        tactic.cases_first=False
        names['balance-'+component]=tactic.theorem('balance-'+component,params,check(f('balance',l,r)),{'Bool':True},guard=guard)
        names['join-right-'+component]=tactic.theorem('join-right-'+component,params,check(f('join_right',l,r)),{'Bool':True},'right',['left'],guard)
        names['join-'+component]=tactic.theorem('join-'+component,params,check(f('join',l,r)),{'Bool':True},'left',['right'],guard)
        names['encode-'+component]=tactic.theorem('encode-'+component,[['xs',D(table)]],check(f('encode',x)),{'Bool':True},'xs')
    guard=binary('&&',valid(l),valid(r))
    for label,operation in [('node','node'),('balance','balance'),('join-right','join_right'),('join','join')]:
        names[label+'-valid']=tactic.theorem(label+'-valid',params,valid(f(operation,l,r)),{'Bool':True},guard=guard)
    names['encode-valid']=tactic.theorem('encode-valid',[['xs',D(table)]],valid(f('encode',x)),{'Bool':True})
    from point_delta import match
    k=var('key');none=cons(option,0,[])
    found=lambda t:f('rows_get',t,k)
    choose_first=lambda a,b:match(a,[([],b),(['found'],cons(option,1,[var('found')]))])
    names['append-get']=tactic.theorem('append-get',[['xs',D(table)],['ys',D(table)],['key','U64']],found(f('append',x,y)),choose_first(found(x),found(y)),'xs')
    names['find-order']=tactic.theorem('find-order',[['tree',D(names['datatype'])],['key','U64']],found(flatten(t)),f('find',t,k),'tree')
    outside=lambda t:binary('||',binary('<',k,f('minimum',t)),binary('>',k,f('maximum',t)))
    names['outside-contains']=tactic.theorem('outside-contains',[['tree',D(names['datatype'])],['key','U64']],f('contains',t,k),{'Bool':False},'tree',guard=binary('&&',valid(t),outside(t)))
    names['absent-find']=tactic.theorem('absent-find',[['tree',D(names['datatype'])],['key','U64']],f('find',t,k),none,'tree',guard=binary('==',f('contains',t,k),{'Bool':False}))
    names['get-find']=tactic.theorem('get-find',[['tree',D(names['datatype'])],['key','U64']],f('get',t,k),f('find',t,k),'tree',guard=valid(t))
    value=var('value')
    for op in ['insert','replace','remove']:
        extra=[]if op=='remove'else[value]
        params=[['tree',D(names['datatype'])],['key','U64']]+([]if op=='remove'else[['value',row_sort]])
        for component in ['minimum_valid','maximum_valid','measure_valid']:
            check=lambda t:f(component,t)
            names[op+'-'+component]=tactic.theorem(op+'-'+component,params,check(f(op,t,k,*extra)),{'Bool':True},'tree',guard=check(t))
        names[op+'-valid']=tactic.theorem(op+'-valid',params,valid(f(op,t,k,*extra)),{'Bool':True},guard=valid(t))
    for op in ['replace','remove','has_key','has_greater']:
        extra=[value]if op=='replace'else[]
        params=[['xs',D(table)],['ys',D(table)],['key','U64']]+([['value',row_sort]]if extra else[])
        combine=(lambda a,b:binary('||',a,b))if op.startswith('has_')else(lambda a,b:f('append',a,b))
        method=op if op.startswith('has_')else'rows_'+op
        names['append-'+op]=tactic.theorem('append-'+op,params,f(method,f('append',x,y),k,*extra),combine(f(method,x,k,*extra),f(method,y,k,*extra)),'xs')
    names['contains-order']=tactic.theorem('contains-order',[['tree',D(names['datatype'])],['key','U64']],f('has_key',flatten(t),k),f('contains',t,k),'tree')
    for op in ['replace','remove']:
        extra=[]if op=='remove'else[value]
        params=[['xs',D(table)],['key','U64']]+([]if op=='remove'else[['value',row_sort]])
        names[op+'-absent']=tactic.theorem(op+'-absent',params,f('rows_'+op,x,k,*extra),x,'xs',guard=binary('==',f('has_key',x,k),{'Bool':False}))
        params[0]=['tree',D(names['datatype'])]
        names[op+'-order']=tactic.theorem(op+'-order',params,f('rows_'+op,flatten(t),k,*extra),flatten(f(op,t,k,*extra)),'tree',guard=valid(t))
    names['greater-order']=tactic.theorem('greater-order',[['tree',D(names['datatype'])],['key','U64']],f('has_greater',flatten(t),k),binary('<',k,f('maximum',t)),'tree',guard=valid(t))
    names['insert-append']=tactic.theorem('insert-append',[['xs',D(table)],['ys',D(table)],['key','U64'],['value',row_sort]],f('rows_insert',f('append',x,y),k,value),{'If':dict(condition=f('has_greater',x,k),on_true=f('append',f('rows_insert',x,k,value),y),on_false=f('append',x,f('rows_insert',y,k,value)))},'xs')
    names['insert-order']=tactic.theorem('insert-order',[['tree',D(names['datatype'])],['key','U64'],['value',row_sort]],f('rows_insert',flatten(t),k,value),flatten(f('insert',t,k,value)),'tree',guard=valid(t))
    return tactic
