"""Guard/field-sensitive stable projection preservation for every query value.

The concrete observation is an Option: None encodes a failed filter guard;
Some contains the projected row. Preserving it proves both guard and fields.
"""
from producers.general_laws import var,call,construct,match,self_call,use
from producers.point_delta import binary,choice,equality

def build(lib):
    R=lib.sort('ProjectionRow');I=lib.sort('ProjectionImage');D=lib.sort('ProjectionChange')
    option=lib.store('ProjectionOption','Datatype',dict(constructors=[dict(name='None',fields=[]),dict(name='Some',fields=[I])]));OS={'Data':option}
    observe=lib.abstract('guarded_row_projection',[R,'U64'],OS);change=lib.abstract('projection_row_change',[R,D],R)
    v,d,q=map(var,('value','change','query'))
    preserves=lib.assumption('guard_and_fields_preserved',[['value',R],['change',D],['query','U64']],call(observe,call(change,v,d),q),call(observe,v,q))
    rows=lib.store('ProjectionSource','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',R,'SelfType'])]));RS={'Data':rows}
    images=lib.store('ProjectedRows','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',I,'SelfType'])]));IS={'Data':images}
    xs,k,h,t=map(var,('rows','key','head','tail'));nil=construct(rows,0);empty=construct(images,0)
    project=lib.function('stable_guarded_projection',[['rows',RS],['query','U64']],IS,match(xs,([],empty),(['head','value','tail'],match(call(observe,v,q),([],self_call(t,q)),(['image'],construct(images,1,h,var('image'),self_call(t,q)))))),0,extra=[option])
    update=lib.function('change_projection_source',[['rows',RS],['key','U64'],['change',D]],RS,match(xs,([],nil),(['head','value','tail'],construct(rows,1,h,choice(binary('==',k,h),call(change,v,d),v),self_call(t,k,d)))),0)
    a=lambda r:call(project,call(update,r,k,d),q);z=lambda r:call(project,r,q)
    bound=construct(rows,1,h,v,t);guard=binary('==',k,h);branches={}
    for flag in (False,True):
        facts=[(guard,{'Bool':flag},1)]
        if flag:facts.append((call(observe,call(change,v,d),q),call(observe,v,q),use(preserves,v,d,q)))
        branches['on_true'if flag else'on_false']=equality(a(bound),z(bound),lib.objects,(a(t),z(t),0),facts)
    proof={'Induction':dict(variable='rows',**{'from':a(xs),'to':z(xs)},cases=[dict(bindings=[],proof=equality(a(nil),z(nil),lib.objects)),dict(bindings=['head','value','tail'],proof={'BoolSplit':dict(condition=guard,**{'from':a(bound),'to':z(bound)},**branches)})])}
    lib.theorem('guarded_projection_does_not_invalidate',[['rows',RS],['key','U64'],['change',D],['query','U64']],a(xs),z(xs),proof,extra=[option])
