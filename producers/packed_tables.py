"""Knowledge-defined inline chunks and universally checked table operations.

Chunk width is a proposal, never a compiler-recognized layout. Arbitrary
constructor chains, duplicate keys and enumeration order are preserved.
"""
from producers.action_replacement import var, call, cons, convert, trans
from producers.point_delta import match, choice, binary
from producers.equational import Tactic, factor


def build(table, objects, add, width=4):
    if type(width) is not int or not 1 <= width <= 4: raise ValueError('packed width must be 1..4')
    logical = table['datatype']; L = {'Data':logical}
    value_sort = objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    option = objects[table['get']]['payload']['declaration']['Function']['result']['Data']
    packed = add({'Datatype':dict(constructors=[dict(name='Empty',fields=[])]+
                  [dict(name='Chunk'+str(n),fields=['U64',value_sort]*n+['SelfType']) for n in range(1,width+1)])})
    P = {'Data':packed}; rows,key,new = map(var,['pack_rows','pack_key','pack_new'])
    nil = cons(packed,0,[]); lnil = cons(logical,0,[])
    names = lambda n: [s+str(i) for i in range(n) for s in ['pack_k','pack_v']]+['pack_tail'] if n else []
    chunk = lambda n: cons(packed,n,[var(x) for x in names(n)])
    def fun(params,result,body,recursive=None):
        return add({'Function':dict(params=params,result=result,body=body,recursive=recursive)})
    def theorem(params,a,z,proof):
        return add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
    def induction(variable,a,z,cases):
        return {'Induction':dict(variable=variable,**{'from':a,'to':z},cases=[dict(bindings=ns,proof=p) for ns,p in cases])}
    def chain(n,tail):
        for i in reversed(range(n)): tail=cons(logical,1,[var('pack_k'+str(i)),var('pack_v'+str(i)),tail])
        return tail
    decode=fun([['pack_rows',P]],L,match(rows,[(names(n),lnil if n==0 else chain(n,{'SelfCall':[var('pack_tail')]})) for n in range(width+1)]),0)
    dec=lambda r:call(decode,[r])
    push=fun([['pack_key','U64'],['pack_new',value_sort],['pack_rows',P]],P,
             match(rows,[(names(n),cons(packed,n+1,[key,new]+([var(x) for x in names(n)] if n else [nil])) if n<width else cons(packed,1,[key,new,rows])) for n in range(width+1)]),2)
    put_head=lambda k,v,r:call(push,[k,v,r])
    # Decode/prepend is the sole storage correspondence used by the proofs.
    a=dec(put_head(key,new,rows));z=cons(logical,1,[key,new,dec(rows)])
    push_law=theorem([['pack_key','U64'],['pack_new',value_sort],['pack_rows',P]],a,z,
        induction('pack_rows',a,z,[(names(n),convert(dec(put_head(key,new,chunk(n))),cons(logical,1,[key,new,dec(chunk(n))]))) for n in range(width+1)]))
    encode=fun([['pack_logical',L]],P,match(var('pack_logical'),[([],nil),(['pack_key','pack_new','pack_rest'],put_head(key,new,{'SelfCall':[var('pack_rest')]}))]),0)
    enc=lambda r:call(encode,[r])
    lr=var('pack_logical');lt=var('pack_rest');head=cons(logical,1,[key,new,lt]);a=dec(enc(lr));z=lr
    middle=cons(logical,1,[key,new,dec(enc(lt))])
    roundtrip=theorem([['pack_logical',L]],a,z,induction('pack_logical',a,z,
        [([],convert(dec(enc(lnil)),lnil)),(['pack_key','pack_new','pack_rest'],trans(
            {'Use':dict(theorem=push_law,arguments=[key,new,enc(lt)],premises=[])},
            {'Construct':dict(datatype=logical,constructor=1,arguments=[{'Refl':key},{'Refl':new},{'Hypothesis':0}])}))]))
    selected={};laws={};tactic=Tactic(objects,[push_law])
    for operation in ['get','remove','replace','insert']:
        params=[['pack_rows',P],['pack_key','U64']]+([['pack_new',value_sort]] if operation in ['replace','insert'] else [])
        args=[key]+([new] if operation in ['replace','insert'] else [])
        branches=[]
        for n in range(width+1):
            tail=var('pack_tail'); recur={'SelfCall':[tail,*args]}
            if operation=='get':
                body=cons(option,0,[]) if n==0 else recur
                for i in reversed(range(n)):body=choice(binary('==',key,var('pack_k'+str(i))),cons(option,1,[var('pack_v'+str(i))]),body)
            elif operation=='replace':
                body=nil if n==0 else cons(packed,n,[x for i in range(n) for x in
                    [var('pack_k'+str(i)),choice(binary('==',key,var('pack_k'+str(i))),new,var('pack_v'+str(i)))]]+[recur])
            elif operation=='remove':
                body=nil if n==0 else recur
                for i in reversed(range(n)):
                    body=choice(binary('==',key,var('pack_k'+str(i))),body,put_head(var('pack_k'+str(i)),var('pack_v'+str(i)),body))
            else:
                body=put_head(key,new,nil) if n==0 else recur
                for i in reversed(range(n)):
                    suffix=cons(packed,n-i,[x for j in range(i,n) for x in [var('pack_k'+str(j)),var('pack_v'+str(j))]]+[tail])
                    body=choice(binary('<',key,var('pack_k'+str(i))),put_head(key,new,suffix),put_head(var('pack_k'+str(i)),var('pack_v'+str(i)),body))
            branches.append((names(n),body))
        f=fun(params,{'Data':option} if operation=='get' else P,match(rows,branches),0)
        selected[operation]=f
        lhs=lambda r:call(f,[r,*args]) if operation=='get' else dec(call(f,[r,*args]))
        rhs=lambda r:call(table[operation],[dec(r),*args])
        cases=[]
        for n in range(width+1):
            hypotheses=[] if n==0 else [(lhs(var('pack_tail')),rhs(var('pack_tail')),0)]
            case_params=params[1:]+[[x, P if x=='pack_tail' else 'U64' if x.startswith('pack_k') else value_sort] for x in names(n)]
            proof=tactic.prove(lhs(chunk(n)),rhs(chunk(n)),hypotheses)
            proof=factor(proof,case_params,[{'from':a,'to':z} for a,z,_ in hypotheses],add)
            cases.append((names(n),proof))
        laws[operation]=theorem(params,lhs(rows),rhs(rows),induction('pack_rows',lhs(rows),rhs(rows),cases))
    # Contains is just the source Option observation of the checked lookup.
    f=fun([['pack_rows',P],['pack_key','U64']],'Bool',match(call(selected['get'],[rows,key]),[([],{'Bool':False}),(['pack_found'],{'Bool':True})]))
    selected['contains']=f
    a=call(f,[rows,key]);z=call(table['contains'],[dec(rows),key])
    context=match(var('delta_hole'),[([],{'Bool':False}),(['pack_found'],{'Bool':True})])
    from producers.point_delta import lift
    laws['contains']=theorem([['pack_rows',P],['pack_key','U64']],a,z,
        trans(convert(a,context_with(context,call(selected['get'],[rows,key]))),lift({'Use':dict(theorem=laws['get'],arguments=[rows,key],premises=[])},context),convert(context_with(context,call(table['get'],[dec(rows),key])),z)))
    return dict(datatype=packed,encode=encode,decode=decode,roundtrip=roundtrip,push=push,push_law=push_law,functions=selected,laws=laws,width=width)


def context_with(context,term):
    from producers.point_delta import sub
    return sub(context,{'delta_hole':term})
