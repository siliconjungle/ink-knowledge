"""Publish type-parametric pipeline laws as data for the generic instantiator.

These equations preserve reducer order; no monoid law or F32 reassociation is
assumed. Only pure total callbacks enter semantic admission. New carriers and
reducers need neither a new producer case nor a backend-specific algorithm.
"""
from ink_knowledge import Store,entry,identity
from ink_knowledge.law_templates import SEMANTICS
from producers.semantic_laws import value,arrow,var,bound,lam,op,law,term

def templates():
    a,b,s=[value({'Named':'$'+n})for n in ('A','B','S')]
    la,lb=value({'List':{'Named':'$A'}}),value({'List':{'Named':'$B'}})
    boolean=value('Bool');xs,ys=var(la,'xs'),var(la,'ys');z=var(s,'z')
    p,q=var(arrow(a,boolean),'p'),var(arrow(a,boolean),'q')
    f=var(arrow(a,b),'f');g=var(arrow(b,s),'g');r=var(arrow(a,arrow(s,s)),'r')
    rb=var(arrow(b,arrow(s,s)),'r');left=var(arrow(a,arrow(s,s)),'step')
    apply=lambda fun,arg:op(fun['sort']['Arrow'][1],'apply',fun,arg)
    reduce=lambda fun,x,acc:apply(apply(fun,x),acc)
    choose=lambda cond,yes,no:op(yes['sort'],'call:choose',cond,yes,no)
    mapping=lambda seq,fun:op(value({'List':fun['sort']['Arrow'][1]['Value']}),'method:map',seq,fun)
    filtering=lambda seq,pred:op(seq['sort'],'method:filter',seq,pred)
    concat=lambda x,y:op(x['sort'],'method:concat',x,y)
    folded=lambda seq,seed,step,direction='foldr':op(seed['sort'],'call:'+direction,seq,seed,step)
    induction=lambda step='Normalize':{'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step=step)}
    cases=lambda cond:{'Cases':dict(condition=cond,on_false='Normalize',on_true='Normalize')}
    rows=[]
    def add(name,names,params,source,target,proof,dependencies=None):
        candidate=law(params,source,target,proof)
        obj=entry('definition',SEMANTICS,dict(type_parameters=names,law=candidate,dependencies=dependencies or {}))
        rows.append(dict(name=name,object=obj))
    add('map-composition',['A','B','S'],dict(xs=la,f=f['sort'],g=g['sort']),mapping(mapping(xs,f),g),
        mapping(xs,lam(a,apply(g,apply(f,bound(a,0))))),induction())
    add('filter-composition',['A'],dict(xs=la,p=p['sort'],q=q['sort']),filtering(filtering(xs,p),q),
        filtering(xs,lam(a,op(boolean,'binary:&&',apply(p,bound(a,0)),apply(q,bound(a,0))))),
        induction(cases(apply(p,var(a,'head')))))
    def chain(before,after,proof):return {'Trans':dict(middle=before,left='Normalize',right={'Trans':dict(middle=after,left=proof,right='Normalize')})}
    tail,head=var(la,'tail'),var(a,'head')
    for direction in ('foldr','foldl'):
        x,acc=bound(a,1),bound(s,0)
        callback=lam(a,lam(s,choose(apply(p,x),reduce(r,x,acc),acc)))
        def filter_step(seed):
            return chain(folded(filtering(tail,p),seed,r,direction),folded(tail,seed,callback,direction),{'GeneralizedHypothesis':dict(index=0,arguments={'z':seed})})
        proof=induction(cases(apply(p,head)))if direction=='foldr'else {'GeneralizedInduction':dict(variable='xs',generalize=['z'],names=['head','tail'],base='Normalize',step={'Cases':dict(condition=apply(p,head),on_false=filter_step(z),on_true=filter_step(reduce(r,head,z)))})}
        add(direction+'-filter',['A','S'],dict(xs=la,z=s,r=r['sort'],p=p['sort']),folded(filtering(xs,p),z,r,direction),
            folded(xs,z,lam(a,lam(s,choose(apply(p,x),reduce(r,x,acc),acc))),direction),
            proof)
        # Ordered concatenation elimination works for every reducer, including
        # records, strings and non-associative floating-point expressions.
        source=folded(concat(xs,ys),z,left,direction)
        target=folded(xs,folded(ys,z,left,direction),left,direction)if direction=='foldr'else folded(ys,folded(xs,z,left,direction),left,direction)
        seed=reduce(left,head,z)
        proof=induction()if direction=='foldr'else {'GeneralizedInduction':dict(variable='xs',generalize=['z'],names=['head','tail'],base='Normalize',step=chain(folded(concat(tail,ys),seed,left,direction),folded(ys,folded(tail,seed,left,direction),left,direction),{'GeneralizedHypothesis':dict(index=0,arguments={'z':seed})}))}
        add(direction+'-concat',['A','S'],dict(xs=la,ys=la,z=s,step=left['sort']),source,target,proof)
    # Map after filtering: preserve the predicate before the mapper and retain
    # the right-fold accumulator grouping. This is a direct reusable endpoint.
    x,acc=bound(a,1),bound(s,0)
    add('foldr-filter-map',['A','B','S'],dict(xs=la,z=s,p=p['sort'],f=f['sort'],r=rb['sort']),
        folded(mapping(filtering(xs,p),f),z,rb),
        folded(xs,z,lam(a,lam(s,choose(apply(p,x),reduce(rb,apply(f,x),acc),acc)))),
        induction(cases(apply(p,var(a,'head')))))
    # Bind the mapped value explicitly rather than duplicating its computation.
    pb=var(arrow(b,boolean),'p');y=bound(b,0);outer_acc=bound(s,1)
    shared=apply(lam(b,choose(apply(pb,y),reduce(rb,y,outer_acc),outer_acc)),apply(f,x))
    add('foldr-map-filter',['A','B','S'],dict(xs=la,z=s,p=pb['sort'],f=f['sort'],r=rb['sort']),
        folded(filtering(mapping(xs,f),pb),z,rb),folded(xs,z,lam(a,lam(s,shared))),
        induction(cases(apply(pb,apply(f,var(a,'head'))))))
    # Both ordered fold directions, without reassociation or monoid assumptions.
    for direction in ('foldr','foldl'):
        callback=lam(a,lam(s,reduce(rb,apply(f,x),acc)))
        seed=reduce(rb,apply(f,head),z)
        proof=induction()if direction=='foldr'else {'GeneralizedInduction':dict(variable='xs',generalize=['z'],names=['head','tail'],base='Normalize',step=chain(folded(mapping(tail,f),seed,rb,direction),folded(tail,seed,callback,direction),{'GeneralizedHypothesis':dict(index=0,arguments={'z':seed})}))}
        add(direction+'-map',['A','B','S'],dict(xs=la,z=s,f=f['sort'],r=rb['sort']),
            folded(mapping(xs,f),z,rb,direction),folded(xs,z,callback,direction),proof)
    for mapped_first in (False,True):
        pred=apply(pb,apply(f,head))if mapped_first else apply(p,head)
        seq=lambda seq:filtering(mapping(seq,f),pb)if mapped_first else mapping(filtering(seq,p),f)
        callback=lam(a,lam(s,shared if mapped_first else choose(apply(p,x),reduce(rb,apply(f,x),acc),acc)))
        def step(seed):
            return chain(folded(seq(tail),seed,rb,'foldl'),folded(tail,seed,callback,'foldl'),{'GeneralizedHypothesis':dict(index=0,arguments={'z':seed})})
        proof={'GeneralizedInduction':dict(variable='xs',generalize=['z'],names=['head','tail'],base='Normalize',step={'Cases':dict(condition=pred,on_false=step(z),on_true=step(reduce(rb,apply(f,head),z)))})}
        add('foldl-'+('map-filter'if mapped_first else'filter-map'),['A','B','S'],dict(xs=la,z=s,p=(pb if mapped_first else p)['sort'],f=f['sort'],r=rb['sort']),folded(seq(xs),z,rb,'foldl'),folded(xs,z,callback,'foldl'),proof)
    # The first replacement in a right fold determines the result. Its predicate
    # and mapper may use arbitrary, different item and accumulator carriers.
    replacement=var(arrow(a,s),'f')
    callback=lam(a,lam(s,choose(apply(p,x),apply(replacement,x),acc)))
    stop=lam(a,lam(s,apply(p,x)))
    add('foldr-first-replacement',['A','S'],dict(xs=la,z=s,p=p['sort'],f=replacement['sort']),
        folded(xs,z,callback),op(s,'call:fold_until',xs,z,stop,callback),induction(cases(apply(p,head))))
    for counter,result in [('count','U64'),('length','U32')]:
        add(counter+'-map',['A','B'],dict(xs=la,f=f['sort']),op(value(result),'call:'+counter,mapping(xs,f)),
            op(value(result),'call:'+counter,xs),induction())
    add('map-identity',['A'],dict(xs=la),mapping(xs,lam(a,bound(a,0))),xs,induction())
    # Carry an Option result: evaluate the predicate once per row. The stop
    # observes an already-found result, so at most one extra row is visited.
    # This representation is ordinary existing source, with an absorbing-state
    # lemma; it requires no new executor primitive or checker matching rule.
    os=value({'Option':{'Named':'$S'}});unit=value('Unit')
    none=op(os,'call:None');some=lambda x:op(os,'call:Some',x)
    unwrap=lambda result:op(s,'method:fold',result,lam(s,bound(s,0)),lam(unit,z))
    stopped=lam(a,lam(os,op(boolean,'method:fold',bound(os,0),lam(s,term(boolean,{'Bool':True})),lam(unit,term(boolean,{'Bool':False})))))
    advanced=lam(a,lam(os,op(os,'method:fold',bound(os,0),lam(s,some(bound(s,0))),lam(unit,choose(apply(p,bound(a,2)),some(apply(replacement,bound(a,2))),none)))))
    controlled=lambda seq,seed:op(os,'call:fold_until',seq,seed,stopped,advanced)
    v=var(s,'v')
    add('fold-until-some-absorption',['A','S'],dict(xs=la,v=s,p=p['sort'],f=replacement['sort']),controlled(xs,some(v)),some(v),induction())
    dependency=identity(rows[-1]['object'])
    mapped_head=apply(replacement,head);terminal=unwrap(some(mapped_head));pending=unwrap(controlled(tail,some(mapped_head)))
    use={'Use':dict(law='$absorbing',arguments=dict(xs=tail,v=mapped_head,p=p,f=replacement),premises=[])}
    true_case={'Trans':dict(middle=terminal,left='Normalize',right={'Sym':{'Trans':dict(middle=pending,left='Normalize',right={'Congruence':[use,'Normalize','Normalize']})}})}
    proof=induction({'Cases':dict(condition=apply(p,head),on_false='Normalize',on_true=true_case)})
    add('foldr-first-option',['A','S'],dict(xs=la,z=s,p=p['sort'],f=replacement['sort']),folded(xs,z,lam(a,lam(s,choose(apply(p,bound(a,1)),apply(replacement,bound(a,1)),bound(s,0))))),unwrap(controlled(xs,none)),proof,{'$absorbing':dependency})
    return rows

def publish(root):
    rows=templates();return Store(root).extend([r['object']for r in rows],{'pipeline-templates/'+r['name']:identity(r['object'])for r in rows})
if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from ink_knowledge import canonical
    p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--export',type=Path);args=p.parse_args()
    if args.export:args.export.write_bytes(canonical(templates())+b'\n')
    print(publish(args.root).snapshot_id)
