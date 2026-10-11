"""Stable indexed-join correspondence, with an explicit ordered-bucket obligation.

No key uniqueness or set semantics: duplicate right rows and left rows retain
full Cartesian multiplicity and left-major/right-major enumeration order.
"""
from producers.general_laws import var,call,construct,match,self_call,refl,congruence,trans,use,hyp
from producers.point_delta import binary,choice,equality,lift
from producers.action_replacement import convert

def build(lib):
    A,B,I=(lib.sort(n)for n in ('JoinLeft','JoinRight','JoinIndex'))
    left=lib.store('JoinLeftRows','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',A,'SelfType'])]))
    right=lib.store('JoinRightRows','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',B,'SelfType'])]))
    bucket=lib.list_of('JoinBucket',B)
    output=lib.store('JoinOutput','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',A,B,'SelfType'])]))
    LS,RS,BS,OS=({'Data':s}for s in (left,right,bucket,output))
    xs,ys,k,a,b,h,t=map(var,('left','right','key','a','b','head','tail'))
    nil=lambda d:construct(d,0)
    out=lambda b,t:construct(output,1,k,a,b,t)
    append=lib.function('join_append',[['xs',OS],['ys',OS]],OS,match(var('xs'),([],var('ys')),(['key','a','b','tail'],out(b,self_call(t,var('ys'))))),0)
    ordered=lib.function('join_ordered_bucket',[['right',RS],['key','U64']],BS,match(ys,([],nil(bucket)),(['head','b','tail'],choice(binary('==',k,h),construct(bucket,1,b,self_call(t,k)),self_call(t,k)))),0)
    expand=lib.function('join_expand_bucket',[['bucket',BS],['key','U64'],['a',A]],OS,match(var('bucket'),([],nil(output)),(['b','tail'],out(b,self_call(t,k,a)))),0)
    scan=lib.function('join_scan_right',[['right',RS],['key','U64'],['a',A]],OS,match(ys,([],nil(output)),(['head','b','tail'],choice(binary('==',k,h),out(b,self_call(t,k,a)),self_call(t,k,a)))),0)
    lhs=lambda r:call(expand,call(ordered,r,k),k,a)
    rhs=lambda r:call(scan,r,k,a)
    bound=construct(right,1,h,b,t);guard=binary('==',k,h)
    branches={}
    for flag in (False,True):
        branches['on_true'if flag else'on_false']=equality(lhs(bound),rhs(bound),lib.objects,(lhs(t),rhs(t),0),[(guard,{'Bool':flag},1)])
    expanded=lib.theorem('join_bucket_expansion_exact',[['right',RS],['key','U64'],['a',A]],lhs(ys),rhs(ys),{'Induction':dict(variable='right',**{'from':lhs(ys),'to':rhs(ys)},cases=[dict(bindings=[],proof=convert(lhs(nil(right)),rhs(nil(right)))),dict(bindings=['head','b','tail'],proof={'BoolSplit':dict(condition=guard,**{'from':lhs(bound),'to':rhs(bound)},**branches)})])})
    encode=lib.abstract('join_build_index',[RS],I);lookup=lib.abstract('join_lookup_bucket',[I,'U64'],BS)
    obligation=lib.assumption('join_bucket_exact',[['right',RS],['key','U64']],call(lookup,call(encode,ys),k),call(ordered,ys,k))
    direct=lib.function('join_nested',[['left',LS],['right',RS]],OS,match(xs,([],nil(output)),(['key','a','tail'],call(append,call(scan,ys,k,a),self_call(t,ys)))),0)
    indexed=lib.function('join_indexed',[['left',LS],['index',I]],OS,match(xs,([],nil(output)),(['key','a','tail'],call(append,call(expand,call(lookup,var('index'),k),k,a),self_call(t,var('index'))))),0)
    lhs=lambda l:call(indexed,l,call(encode,ys));rhs=lambda l:call(direct,l,ys)
    first=trans(congruence(expand,use(obligation,ys,k),refl(k),refl(a)),use(expanded,ys,k,a))
    lib.theorem('join_indexed_exact',[['left',LS],['right',RS]],lhs(xs),rhs(xs),{'Induction':dict(variable='left',**{'from':lhs(xs),'to':rhs(xs)},cases=[dict(bindings=[],proof=convert(lhs(nil(left)),rhs(nil(left)))),dict(bindings=['key','a','tail'],proof=congruence(append,first,hyp(0)))])})
