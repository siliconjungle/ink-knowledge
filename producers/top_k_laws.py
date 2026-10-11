"""Untrusted stable insertion-prefix proofs. No ordering axioms are needed.

The bounded result equals the prefix of the exact full insertion fold even for an
arbitrary total predicate. Interpreting it as ordered top-k additionally requires
a strict ordering predicate. This model is not an automatic source rewrite.
"""
from producers.general_laws import var,call,construct,match,self_call,refl,congruence,construct_congruence,use,sym,trans

def generalized(variable,generalize,left,right,cases):
    return {'GeneralizedInduction':dict(variable=variable,generalize=generalize,**{'from':left,'to':right},cases=[dict(bindings=b,proof=p)for b,p in cases])}
def induction(variable,left,right,cases):
    return {'Induction':dict(variable=variable,**{'from':left,'to':right},cases=[dict(bindings=b,proof=p)for b,p in cases])}
def ih(*args):return {'GeneralizedHypothesis':dict(index=0,arguments=list(args))}

def build(lib):
    from producers.point_delta import choice,equality
    E={'Data':lib.names['Element']};L=lib.names['Rows'];LS={'Data':L}
    N=lib.store('Capacity','Datatype',dict(constructors=[dict(name='Zero',fields=[]),dict(name='Successor',fields=['SelfType'])]));NS={'Data':N}
    zero=construct(N,0);succ=lambda n:construct(N,1,n)
    nil=construct(L,0);cons=lambda h,t:construct(L,1,h,t)
    cap,xs,rest,head,tail,item=map(var,('capacity','xs','rest','head','tail','item'))
    take=lib.function('take_prefix',[['capacity',NS],['xs',LS]],LS,match(cap,([],nil),(['rest'],match(xs,([],nil),(['head','tail'],cons(head,self_call(rest,tail)))))),0)
    T=lambda cap,xs:call(take,cap,xs)
    left=T(cap,T(succ(cap),xs));right=T(cap,xs)
    inner=induction('xs',T(succ(rest),T(succ(succ(rest)),xs)),T(succ(rest),xs),[
        ([],refl(nil)),(['head','tail'],construct_congruence(L,1,refl(head),ih(tail)))])
    prefix=lib.theorem('shorter_prefix_of_prefix',[['capacity',NS],['xs',LS]],left,right,
        generalized('capacity',['xs'],left,right,[([],refl(nil)),(['rest'],inner)]))
    less=lib.abstract('strictly_before',[E,E],'Bool')
    insert=lib.function('ordered_insert',[['item',E],['xs',LS]],LS,match(xs,([],cons(item,nil)),(['head','tail'],choice(call(less,item,head),cons(item,xs),cons(head,self_call(item,tail))))),1)
    I=lambda item,xs:call(insert,item,xs)
    left=T(cap,I(item,T(cap,xs)));right=T(cap,I(item,xs))
    bound=cons(head,tail);a=T(succ(rest),I(item,T(succ(rest),bound)));z=T(succ(rest),I(item,bound))
    guard=call(less,item,head)
    # The authoring tactic transports the prefix/induction equality through the
    # exact enclosing Cons after rewriting the single comparison condition.
    from producers.point_delta import normal,replace,lift
    def close(flag,middle):
        from producers.action_replacement import alpha_normal
        na,nz=alpha_normal(normal(a,lib.objects)),alpha_normal(normal(z,lib.objects));hole=var('delta_hole');h={'Hypothesis':1}
        ca,cz=replace(na,guard,hole),replace(nz,guard,hole)
        fa,fz=replace(na,guard,{'Bool':flag}),replace(nz,guard,{'Bool':flag})
        from producers.action_replacement import convert
        return trans(convert(a,na),lift(h,ca),convert(fa,middle[0]),middle[2],convert(middle[1],fz),sym(lift(h,cz)),convert(nz,z))
    truel=cons(item,T(rest,T(succ(rest),bound)));truer=cons(item,T(rest,bound))
    yes=close(True,(truel,truer,construct_congruence(L,1,refl(item),use(prefix,rest,bound))))
    falsel=cons(head,T(rest,I(item,T(rest,tail))));falser=cons(head,T(rest,I(item,tail)))
    no=close(False,(falsel,falser,construct_congruence(L,1,refl(head),ih(tail))))
    step={'BoolSplit':dict(condition=guard,**{'from':a,'to':z},on_false=no,on_true=yes)}
    inner=induction('xs',T(succ(rest),I(item,T(succ(rest),xs))),T(succ(rest),I(item,xs)),[( [],refl(cons(item,T(rest,nil))) ),(['head','tail'],step)])
    commute=lib.theorem('prefix_insert_commutes',[['capacity',NS],['xs',LS],['item',E]],left,right,
        generalized('capacity',['xs'],left,right,[([],refl(nil)),(['rest'],inner)]))
    initial=var('initial')
    full=lib.function('insertion_fold',[['xs',LS],['initial',LS]],LS,match(xs,([],initial),(['head','tail'],self_call(tail,I(head,initial)))),0)
    bounded=lib.function('bounded_insertion_fold',[['xs',LS],['capacity',NS],['initial',LS]],LS,match(xs,([],initial),(['head','tail'],self_call(tail,cap,T(cap,I(head,initial))))),0)
    F=lambda xs,initial:call(full,xs,initial);B=lambda xs,initial:call(bounded,xs,cap,initial)
    left=B(xs,T(cap,initial));right=T(cap,F(xs,initial))
    step=trans(congruence(bounded,refl(tail),refl(cap),use(commute,cap,initial,head)),ih(I(head,initial)))
    lib.theorem('bounded_insertion_fold_exact',[['xs',LS],['capacity',NS],['initial',LS]],left,right,
        generalized('xs',['initial'],left,right,[([],refl(T(cap,initial))),(['head','tail'],step)]))
