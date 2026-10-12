"""Erased cardinality refinements in exact integers, proved by general induction
and integer inequality certificates. Wrapped U32/U64 counts are deliberately not
used as mathematical allocation bounds."""
from producers.semantic_laws import value,arrow,var,word,op,term,law
from ink_knowledge import Store,semantic_entry,identity

def examples():
    result={};b=value('Bool');c=value('Int');true=term(b,{'Bool':True})
    for t in ('U32','I32','U64','F32','Bool'):
        s=value(t);ls=value({'List':t});xs=var(ls,'xs');ps=arrow(s,b);p=var(ps,'p')
        count=lambda x:op(c,'call:count',x)
        filtered=op(ls,'method:filter',xs,p)
        induction={'Induction':dict(variable='xs',names=['head','tail'],base={'Linear':dict(premises=[])},step={'Cases':dict(condition=op(b,'apply',p,var(s,'head')),on_false={'Linear':dict(premises=[[0,1]])},on_true={'Linear':dict(premises=[[0,1]])})})}
        result['refinements/filter-bound-'+t.lower()]=law(dict(xs=ls,p=ps),op(b,'binary:<=',count(filtered),count(xs)),true,induction)
        proof={'Induction':dict(variable='xs',names=['head','tail'],base={'Linear':dict(premises=[])},step={'Linear':dict(premises=[[0,1]])})}
        result['refinements/count-nonnegative-'+t.lower()]=law(dict(xs=ls),op(b,'binary:<=',word('Int',0),count(xs)),true,proof)
        for target in ('U32','I32','U64','F32','Bool'):
            ts=value(target);lt=value({'List':target});fs=arrow(s,ts);f=var(fs,'f')
            result['refinements/map-count-'+t.lower()+'-'+target.lower()]=law(dict(xs=ls,f=fs),count(op(lt,'method:map',xs,f)),count(xs),{'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step='Normalize')})
    return result

def publish(root):
    store=Store(root);objects=[];names={}
    for name,l in examples().items():
        obj=semantic_entry(l);objects.append(obj);names['rewrite/'+name]=identity(obj)
    return store.extend(objects,names)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output-store',required=True);a=p.parse_args()
    print(publish(a.output_store).snapshot_id)
