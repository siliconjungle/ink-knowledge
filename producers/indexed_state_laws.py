"""Stable partition indexes: arbitrary keys, duplicate rows and input order.

The source rows remain the enumeration/codec spine. Index buckets are maintained
separately; lookup visits one bucket, remove/replace repair each bucket directly.
Insertion refreshes because arbitrary logical lists need not be sorted. A concrete
key partition must discharge the equality congruence obligation.
"""
from producers.general_laws import var,call,construct,match,self_call,use,hyp,refl,trans
from producers.point_delta import binary,choice,equality

def build(lib):
    R=lib.sort('IndexedRow');rows=lib.store('IndexedRows','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',R,'SelfType'])]));RS={'Data':rows}
    option=lib.store('IndexedOption','Datatype',dict(constructors=[dict(name='None',fields=[]),dict(name='Some',fields=[R])]));OS={'Data':option}
    predicate=lib.abstract('key_partition',['U64'],'Bool')
    q,k,h,x,t,r,n=map(var,('query','key','head','value','tail','rows','new'))
    p=lambda k:call(predicate,k);eq=lambda a,b:binary('==',a,b)
    agrees=lib.store('equal_keys_have_equal_partition','Assumption',dict(params=[['query','U64'],['head','U64']],conditions=[dict(**{'from':eq(q,h),'to':{'Bool':True}})],**{'from':p(q),'to':p(h)}))
    nil=construct(rows,0);none=construct(option,0);cons=lambda h,x,t:construct(rows,1,h,x,t)
    get=lib.function('indexed_source_get',[['rows',RS],['query','U64']],OS,match(r,([],none),(['head','value','tail'],choice(eq(q,h),construct(option,1,x),self_call(t,q)))),0)
    remove=lib.function('indexed_source_remove',[['rows',RS],['key','U64']],RS,match(r,([],nil),(['head','value','tail'],choice(eq(k,h),self_call(t,k),cons(h,x,self_call(t,k))))),0)
    replace=lib.function('indexed_source_replace',[['rows',RS],['key','U64'],['new',R]],RS,match(r,([],nil),(['head','value','tail'],cons(h,choice(eq(k,h),n,x),self_call(t,k,n)))),0)
    filters={}
    for flag in (False,True):
        filters[flag]=lib.function('partition_'+str(flag).lower(),[['rows',RS]],RS,match(r,([],nil),(['head','value','tail'],choice(p(h),cons(h,x,self_call(t)) if flag else self_call(t),self_call(t) if flag else cons(h,x,self_call(t))))),0)
    split=lambda r:choice(p(q),call(get,call(filters[True],r),q),call(get,call(filters[False],r),q))
    right=lambda r:call(get,r,q)
    bound=cons(h,x,t);guard=eq(q,h)
    branches={}
    for same in (False,True):
        facts=[(guard,{'Bool':same},1)]
        if same:facts.append((p(q),p(h),{'Use':dict(theorem=agrees,arguments=[q,h],premises=[hyp(1)])}))
        subbranches={}
        for flag in (False,True):
            fs=[*facts,(p(h),{'Bool':flag},2)]
            # A nonmatching head delegates to precisely the same bucket choice.
            subbranches['on_true' if flag else 'on_false']=equality(split(bound),right(bound),lib.objects,(split(t),right(t),0),fs)
        branches['on_true'if same else'on_false']={'BoolSplit':dict(condition=p(h),**{'from':split(bound),'to':right(bound)},**subbranches)}
    empty={'BoolSplit':dict(condition=p(q),**{'from':split(nil),'to':right(nil)},on_false=equality(split(nil),right(nil),lib.objects,facts=[(p(q),{'Bool':False},0)]),on_true=equality(split(nil),right(nil),lib.objects,facts=[(p(q),{'Bool':True},0)]))}
    proof={'Induction':dict(variable='rows',**{'from':split(r),'to':right(r)},cases=[dict(bindings=[],proof=empty),dict(bindings=['head','value','tail'],proof={'BoolSplit':dict(condition=guard,**{'from':split(bound),'to':right(bound)},**branches)})])}
    lib.theorem('partition_lookup_exact',[['rows',RS],['query','U64']],split(r),right(r),proof)
    for flag in (False,True):
        F=lambda r:call(filters[flag],r)
        for name,op,extra in [('remove',lambda r:call(remove,r,k),[]),('replace',lambda r:call(replace,r,k,n),[['new',R]])]:
            a=lambda r:F(op(r));z=lambda r:op(F(r));branches={}
            for selected in (False,True):
                leaves={}
                for same in (False,True):
                    leaves['on_true'if same else'on_false']=equality(a(bound),z(bound),lib.objects,(a(t),z(t),0),[(p(h),{'Bool':selected},1),(eq(k,h),{'Bool':same},2)])
                branches['on_true'if selected else'on_false']={'BoolSplit':dict(condition=eq(k,h),**{'from':a(bound),'to':z(bound)},**leaves)}
            step={'BoolSplit':dict(condition=p(h),**{'from':a(bound),'to':z(bound)},**branches)}
            proof={'Induction':dict(variable='rows',**{'from':a(r),'to':z(r)},cases=[dict(bindings=[],proof=equality(a(nil),z(nil),lib.objects)),dict(bindings=['head','value','tail'],proof=step)])}
            lib.theorem('partition_'+str(flag).lower()+'_'+name,[['rows',RS],['key','U64']]+extra,a(r),z(r),proof)
    physical=lib.store('PartitionIndex','Datatype',dict(constructors=[dict(name='Index',fields=[RS,RS,RS])]));PS={'Data':physical}
    enc=lib.function('partition_encode',[['rows',RS]],PS,construct(physical,0,r,call(filters[False],r),call(filters[True],r)))
    dec=lib.function('partition_decode',[['physical',PS]],RS,match(var('physical'),(['rows','low','high'],r)))
    lookup=lib.function('partition_lookup',[['physical',PS],['query','U64']],OS,match(var('physical'),(['rows','low','high'],choice(p(q),call(get,var('high'),q),call(get,var('low'),q)))))
    lib.theorem('partition_codec_roundtrip',[['rows',RS]],call(dec,call(enc,r)),r,refl(r))
    lib.theorem('partition_encoded_lookup',[['rows',RS],['query','U64']],call(lookup,call(enc,r),q),right(r),use(lib.names['partition_lookup_exact'],r,q))
    for name,fn,extra,args in [('remove',remove,[],[k]),('replace',replace,[['new',R]],[k,n])]:
        repair=lib.function('partition_repair_'+name,[['physical',PS],['key','U64']]+extra,PS,match(var('physical'),(['rows','low','high'],construct(physical,0,call(fn,r,*args),call(fn,var('low'),*args),call(fn,var('high'),*args)))))
        a=call(repair,call(enc,r),*args);z=call(enc,call(fn,r,*args))
        proof={'Construct':dict(datatype=physical,constructor=0,arguments=[refl(call(fn,r,*args)),{'Sym':use(lib.names['partition_false_'+name],r,*args)},{'Sym':use(lib.names['partition_true_'+name],r,*args)}])}
        lib.theorem('partition_repair_'+name+'_exact',[['rows',RS],['key','U64']]+extra,a,z,proof)
