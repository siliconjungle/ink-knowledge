"""Profile-proposed hot-key indexes over any checked packed table layout.

All other keys use the underlying lookup. Writes refresh the auxiliary index;
no uniqueness, sorting or profile frequency is a correctness assumption.
"""
from producers.action_replacement import var, call, cons, convert
from producers.point_delta import match, choice, binary
from producers.equational import Tactic, factor


def build(table, base, objects, add, keys, equality_law):
    keys=sorted(set(keys))
    if not keys or len(keys)>8 or any(type(k) is not int or not 0<=k<1<<64 for k in keys):raise ValueError('hot keys must be 1..8 u64 values')
    C={'Data':base['datatype']};L={'Data':table['datatype']}
    option=objects[table['get']]['payload']['declaration']['Function']['result']
    value_sort=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    indexed=add({'Datatype':dict(constructors=[dict(name='IndexedChunks',fields=[C,*[option for _ in keys]])])});P={'Data':indexed}
    names=['index_rows',*['index_value_'+str(i) for i in range(len(keys))]]
    root=var('index_root');rows=var('index_rows');key=var('index_key');new=var('index_new')
    bound=cons(indexed,0,[var(n) for n in names])
    def fun(params,result,body,recursive=None):return add({'Function':dict(params=params,result=result,body=body,recursive=recursive)})
    def theorem(params,a,z,proof):return add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
    def induction(a,z,p):return {'Induction':dict(variable='index_root',**{'from':a,'to':z},cases=[dict(bindings=names,proof=p)])}
    refresh_chunks=fun([['index_rows',C]],P,cons(indexed,0,[rows,*[call(base['functions']['get'],[rows,{'U64':k}]) for k in keys]]))
    refresh=lambda r:call(refresh_chunks,[r])
    fresh=fun([['index_root',P]],P,match(root,[(names,refresh(rows))]),0)
    freshof=lambda r:call(fresh,[r])
    encode=fun([['index_logical',L]],P,refresh(call(base['encode'],[var('index_logical')])))
    decode=fun([['index_root',P]],L,match(root,[(names,call(base['decode'],[rows]))]),0)
    dec=lambda r:call(decode,[r])
    params=[['index_root',P],['index_key','U64']]
    branch=call(base['functions']['get'],[rows,key])
    for i,k in reversed(list(enumerate(keys))):branch=choice(binary('==',key,{'U64':k}),var(names[i+1]),branch)
    selected={'get':fun(params,option,match(root,[(names,branch)]),0)}
    rules=[*base['laws'].values(),equality_law]
    tactic=Tactic(objects,rules)
    a=call(selected['get'],[freshof(root),key]);z=call(table['get'],[dec(root),key])
    proof=tactic.prove(call(selected['get'],[freshof(bound),key]),call(table['get'],[dec(bound),key]))
    proof=factor(proof,params[1:]+list(zip(names,[C,*[option for _ in keys]])),[],add)
    laws={'get':theorem(params,a,z,induction(a,z,proof))}
    selected['contains']=fun(params,'Bool',match(call(selected['get'],[root,key]),[([],{'Bool':False}),(['index_found'],{'Bool':True})]))
    a=call(selected['contains'],[freshof(root),key]);z=call(table['contains'],[dec(root),key])
    laws['contains']=theorem(params,a,z,Tactic(objects,[laws['get']]).prove(a,z))
    for op in ['remove','replace','insert']:
        params=[['index_root',P],['index_key','U64']]+([['index_new',value_sort]] if op!='remove' else [])
        args=[key]+([new] if op!='remove' else [])
        selected[op]=fun(params,P,match(root,[(names,refresh(call(base['functions'][op],[rows,*args])))]),0)
        a=dec(call(selected[op],[root,*args]));z=call(table[op],[dec(root),*args])
        laws[op]=theorem(params,a,z,induction(a,z,tactic.prove(dec(call(selected[op],[bound,*args])),call(table[op],[dec(bound),*args]))))
    a=dec(freshof(root));z=dec(root)
    fresh_decode=theorem([['index_root',P]],a,z,induction(a,z,convert(dec(freshof(bound)),dec(bound))))
    a=freshof(freshof(root));z=freshof(root)
    idempotent=theorem([['index_root',P]],a,z,induction(a,z,convert(freshof(freshof(bound)),freshof(bound))))
    fresh_laws=[idempotent,fresh_decode]
    for op in ['remove','replace','insert']:
        args=[key]+([new] if op!='remove' else [])
        params=[['index_root',P],['index_key','U64']]+([['index_new',value_sort]] if op!='remove' else [])
        changed=call(selected[op],[root,*args]);a=freshof(changed)
        concrete=call(selected[op],[bound,*args])
        fresh_laws.append(theorem(params,a,changed,induction(a,changed,convert(freshof(concrete),concrete))))
        query=var('index_query')
        a=call(selected['get'],[changed,query]);z=call(table['get'],[call(table[op],[dec(root),*args]),query])
        proof=tactic.prove(call(selected['get'],[concrete,query]),call(table['get'],[call(table[op],[dec(bound),*args]),query]))
        proof=factor(proof,params[1:]+[['index_query','U64']]+list(zip(names,[C,*[option for _ in keys]])),[],add)
        laws['get-after-'+op]=theorem([*params,['index_query','U64']],a,z,induction(a,z,proof))
    a=call(decode,[call(encode,[var('index_logical')])]);z=var('index_logical')
    rt=theorem([['index_logical',L]],a,z,Tactic(objects,[*base['laws'].values(),base['roundtrip']]).prove(a,z))
    return dict(datatype=indexed,encode=encode,decode=decode,roundtrip=rt,functions=selected,laws=laws,
                fresh=fresh,fresh_laws=fresh_laws,keys=keys,width=base['width'],base=base)
