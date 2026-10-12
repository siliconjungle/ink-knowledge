"""Data-owned elimination of traversals and temporary concatenations.

All equations use existing total collection semantics. Ordered folds keep the
seed exactly; cardinality additions retain the source width's wrapping meaning.
"""
from ink_knowledge import Store,entry,identity
from ink_knowledge.law_templates import SEMANTICS
from producers.semantic_laws import value,var,op,lam,bound,term,law

def templates():
    a,s=value({'Named':'$A'}),value({'Named':'$S'})
    seq=value({'List':{'Named':'$A'}});xs,ys=var(seq,'xs'),var(seq,'ys')
    boolean=value('Bool');z=var(s,'z');rows=[]
    induction={'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step='Normalize')}
    def add(name,names,params,source,target,proof=induction):
        obj=entry('definition',SEMANTICS,dict(type_parameters=names,law=law(params,source,target,proof),dependencies={}))
        rows.append(dict(name=name,object=obj))
    for flag in (False,True):
        source=op(seq,'method:filter',xs,lam(a,term(boolean,{'Bool':flag})))
        add('filter-'+str(flag).lower(),['A'],{'xs':seq},source,xs if flag else term(seq,'Nil'))
    for direction in ('foldl','foldr'):
        add(direction+'-unchanged',['A','S'],dict(xs=seq,z=s),op(s,'call:'+direction,xs,z,lam(a,lam(s,bound(s,0)))),z)
    for counter,kind in [('length','U32'),('count','U64')]:
        result=value(kind);count=lambda x:op(result,'call:'+counter,x)
        add(counter+'-concat',['A'],dict(xs=seq,ys=seq),count(op(seq,'method:concat',xs,ys)),op(result,'binary:+',count(xs),count(ys)))
    return rows

def publish(root):
    rows=templates()
    return Store(root).extend([r['object']for r in rows],{'traversal-templates/'+r['name']:identity(r['object'])for r in rows})
