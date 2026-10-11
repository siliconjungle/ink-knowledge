"""Parameterised group/filter aggregate deltas over arbitrary keyed row lists.

Contribution(row, query) can encode group membership, filter guards and fields.
All duplicates contribute. Scalar identities use independently replayed word
certificates; concrete interpretations must match the exact contribution.
"""
from producers.general_laws import var,call,construct,match,self_call,refl,trans
from producers.point_delta import binary,choice,equality,normal,lift
from producers.action_replacement import convert
from producers.word_ring import Tactic,free
from producers.workspace import compiler_path

def build(lib):
    R=lib.sort('AggregateRow');contribution=lib.abstract('group_contribution',[R,'U64'],'U64')
    rows=lib.store('AggregateRows','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',R,'SelfType'])]));RS={'Data':rows}
    r,k,q,h,v,t,n=map(var,('rows','key','query','head','value','tail','new'))
    nil=construct(rows,0);cons=lambda h,v,t:construct(rows,1,h,v,t);C=lambda v:call(contribution,v,q)
    total=lib.function('group_total',[['rows',RS],['query','U64']],'U64',match(r,([],{'U64':0}),(['head','value','tail'],binary('+',C(v),self_call(t,q)))),0)
    remove=lib.function('group_source_remove',[['rows',RS],['key','U64']],RS,match(r,([],nil),(['head','value','tail'],choice(binary('==',k,h),self_call(t,k),cons(h,v,self_call(t,k))))),0)
    replace=lib.function('group_source_replace',[['rows',RS],['key','U64'],['new',R]],RS,match(r,([],nil),(['head','value','tail'],cons(h,choice(binary('==',k,h),n,v),self_call(t,k,n)))),0)
    def add(declaration):
        body=declaration['Theorem'];return lib.store('group_word_lemma_'+str(len(lib.objects)),'Theorem',body)
    from pathlib import Path
    ring=Tactic(add,compiler_path(),Path(__file__).resolve().parents[1]/'research/composable-state/word-certificates')
    a,b,c=map(var,('a','b','c'));zero={'U64':0};neg=lambda x:binary('-',zero,x)
    axioms={
        'assoc':(binary('+',binary('+',a,b),c),binary('+',a,binary('+',b,c))),
        'commute':(binary('+',a,b),binary('+',b,a)),
        'zero':(binary('+',a,zero),a),'left_zero':(binary('+',zero,a),a),
        'inverse':(binary('+',a,neg(a)),zero),
        'subtract':(binary('-',a,b),binary('+',a,neg(b))),
        'negate_add':(neg(binary('+',a,b)),binary('+',neg(a),neg(b))),
        'double_negate':(neg(neg(a)),a),
    }
    for name,(left,right)in axioms.items():
        params=[[name,'U64']for name in sorted(free(left)|free(right))]
        ring.law(name,[var(n)for n,_ in params]);lib.names['group_word_'+name]=ring.laws[name][0]
    memo={}
    def arithmetic(left,right):
        opaque=[]
        def abstract(term):
            if 'U64'in term:return term
            if 'Binary'in term and term['Binary']['op']in ('+','-'):
                x=term['Binary'];return binary(x['op'],abstract(x['left']),abstract(x['right']))
            if term not in opaque:opaque.append(term)
            return var('word_'+str(opaque.index(term)))
        a,z=abstract(left),abstract(right)
        import json
        key=json.dumps([a,z],sort_keys=True)
        if key not in memo:memo[key]=lib.theorem('group_scalar_'+str(len(memo)),[['word_'+str(i),'U64']for i in range(len(opaque))],a,z,ring.prove(a,z))
        return {'Use':dict(theorem=memo[key],arguments=opaque,premises=[])}
    for name,op,extra,args in [('remove',remove,[],[k]),('replace',replace,[['new',R]],[k,n])]:
        difference=binary('-',zero if name=='remove'else C(n),C(v))
        delta=lib.function('group_delta_'+name,[['rows',RS],['key','U64'],['query','U64']]+extra,'U64',match(r,([],zero),(['head','value','tail'],binary('+',choice(binary('==',k,h),difference,zero),self_call(t,k,q,*([n]if name=='replace'else[]))))),0)
        lhs=lambda r:call(total,call(op,r,*args),q)
        rhs=lambda r:binary('+',call(total,r,q),call(delta,r,k,q,*([n]if name=='replace'else[])))
        bound=cons(h,v,t);guard=binary('==',k,h);branches={}
        for flag in (False,True):
            facts=[(guard,{'Bool':flag},1)]
            # First normalise and substitute the exact induction hypothesis,
            # then discharge the remaining scalar permutation/cancellation.
            left,right=normal(lhs(bound),lib.objects),normal(rhs(bound),lib.objects)
            from producers.point_delta import replace as rewrite
            left=rewrite(left,guard,{'Bool':flag});right=rewrite(right,guard,{'Bool':flag})
            left,right=normal(left,lib.objects),normal(right,lib.objects)
            ih_left,ih_right=lhs(t),rhs(t);changed=rewrite(left,ih_left,ih_right)
            scalar=arithmetic(changed,right)
            # equality() also rewrites the hypothesis under branch facts.
            bridge=equality(lhs(bound),changed,lib.objects,(ih_left,ih_right,0),facts)
            finish=equality(rhs(bound),right,lib.objects,facts=facts)
            branches['on_true'if flag else'on_false']=trans(bridge,scalar,{'Sym':finish})
        empty=arithmetic(normal(lhs(nil),lib.objects),normal(rhs(nil),lib.objects))
        proof={'Induction':dict(variable='rows',**{'from':lhs(r),'to':rhs(r)},cases=[dict(bindings=[],proof=empty),dict(bindings=['head','value','tail'],proof={'BoolSplit':dict(condition=guard,**{'from':lhs(bound),'to':rhs(bound)},**branches)})])}
        lib.theorem('group_'+name+'_repair_exact',[['rows',RS],['key','U64'],['query','U64']]+extra,lhs(r),rhs(r),proof)
