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
    def add(name,names,params,source,target,proof):
        candidate=law(params,source,target,proof)
        obj=entry('definition',SEMANTICS,dict(type_parameters=names,law=candidate,dependencies={}))
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
    for counter,result in [('count','U64'),('length','U32')]:
        add(counter+'-map',['A','B'],dict(xs=la,f=f['sort']),op(value(result),'call:'+counter,mapping(xs,f)),
            op(value(result),'call:'+counter,xs),induction())
    add('map-identity',['A'],dict(xs=la),mapping(xs,lam(a,bound(a,0))),xs,induction())
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
