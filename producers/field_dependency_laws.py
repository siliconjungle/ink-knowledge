"""Untrusted field-sensitive dependency law on every key and row sequence.

The caller proves that its actual row update preserves the observed projection.
No metadata declaration of a field dependency can discharge that obligation.
"""
from producers.general_laws import var,call,construct,match,self_call,use,hyp

def build(lib):
    from producers.point_delta import binary,choice,equality
    R=lib.sort('DependencyRow');F=lib.sort('ObservedField');D=lib.sort('OtherFieldChange')
    observe=lib.abstract('observe_field',[R],F);change=lib.abstract('change_other_field',[R,D],R)
    row,delta=var('row'),var('change')
    preserves=lib.assumption('other_field_preserves_observation',[['row',R],['change',D]],call(observe,call(change,row,delta)),call(observe,row))
    rows=lib.store('DependencyRows','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',R,'SelfType'])]));RS={'Data':rows}
    option=lib.store('FieldOption','Datatype',dict(constructors=[dict(name='None',fields=[]),dict(name='Some',fields=[F])]));OS={'Data':option}
    xs,key,q,h,v,t=map(var,('rows','key','query','head','value','tail'))
    query=lib.function('lookup_observed_field',[['rows',RS],['query','U64']],OS,match(xs,([],construct(option,0)),(['head','value','tail'],choice(binary('==',q,h),construct(option,1,call(observe,v)),self_call(t,q)))),0)
    update=lib.function('write_other_field',[['rows',RS],['key','U64'],['change',D]],RS,match(xs,([],construct(rows,0)),(['head','value','tail'],construct(rows,1,h,choice(binary('==',key,h),call(change,v,delta),v),self_call(t,key,delta)))),0)
    h,v,t=map(var,('proof_key','proof_row','proof_tail'));bound=construct(rows,1,h,v,t)
    left=lambda xs:call(query,call(update,xs,key,delta),q);right=lambda xs:call(query,xs,q)
    qguard=binary('==',q,h);wguard=binary('==',key,h)
    no=equality(left(bound),right(bound),lib.objects,(left(t),right(t),0),[(qguard,{'Bool':False},1)])
    yes_no=equality(left(bound),right(bound),lib.objects,facts=[(qguard,{'Bool':True},1),(wguard,{'Bool':False},2)])
    field_proof={'Use':dict(theorem=preserves,arguments=[v,delta],premises=[])}
    yes_yes=equality(left(bound),right(bound),lib.objects,(call(observe,call(change,v,delta)),call(observe,v),field_proof),[(qguard,{'Bool':True},1),(wguard,{'Bool':True},2)])
    yes={'BoolSplit':dict(condition=wguard,**{'from':left(bound),'to':right(bound)},on_false=yes_no,on_true=yes_yes)}
    step={'BoolSplit':dict(condition=qguard,**{'from':left(bound),'to':right(bound)},on_false=no,on_true=yes)}
    nil=construct(rows,0)
    proof={'Induction':dict(variable='rows',**{'from':left(xs),'to':right(xs)},cases=[dict(bindings=[],proof=equality(left(nil),right(nil),lib.objects)),dict(bindings=['proof_key','proof_row','proof_tail'],proof=step)])}
    lib.theorem('other_field_does_not_invalidate_lookup',[['rows',RS],['key','U64'],['query','U64'],['change',D]],left(xs),right(xs),proof)
