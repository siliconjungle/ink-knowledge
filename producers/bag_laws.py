"""Universal multiplicity proofs for sorting, and extensional observer tools.

Insertion and sorting preserve the count of every possible word value. Ordinary
induction, cases, arithmetic, and named function extensionality establish this;
there is no privileged bag/sort proof rule in the compiler.
"""
from producers.semantic_laws import value,var,word,op,law,lam,bound,term
from ink_knowledge import semantic_entry,identity

def shift(term,depth=0):
    import copy
    result=copy.deepcopy(term);node=result['node']
    if isinstance(node,dict):
        if 'Bound'in node and node['Bound']>=depth:node['Bound']+=1
        elif 'Lambda'in node:node['Lambda']=shift(node['Lambda'],depth+1)
        elif 'Op'in node:node['Op'][1]=[shift(x,depth)for x in node['Op'][1]]
        elif 'Cons'in node:node['Cons']=[shift(x,depth)for x in node['Cons']]
    return result

def examples():
    rows={};boolean=value('Bool');count_sort=value('Int')
    for ty in ('U32','U64','I32'):
        scalar=value(ty);sequence=value({'List':ty});xs=var(sequence,'xs');item=var(scalar,'item');x=var(scalar,'x');head=var(scalar,'head');tail=var(sequence,'tail')
        equal=lambda a,b:op(boolean,'value:equal',a,b)
        count=lambda ys,k:op(count_sort,'call:count',op(sequence,'method:filter',ys,lam(scalar,equal(bound(scalar,0),shift(k)))))
        delta=lambda k:op(count_sort,'call:choose',equal(k,item),word('Int',1),word('Int',0))
        insert=lambda k,ys:op(sequence,'list.insert',k,ys)
        plus=lambda a,b:op(count_sort,'binary:+',a,b)
        cases=lambda condition:{'Cases':dict(condition=condition,on_false='Normalize',on_true='Normalize')}
        step={'Cases':dict(condition=op(boolean,'binary:<=',x,head),on_true=cases(equal(x,item)),on_false=cases(equal(head,item)))}
        name='bags/insert-occurrences-'+ty.lower()
        helper=law(dict(xs=sequence,x=scalar,item=scalar),count(insert(x,xs),item),plus(delta(x),count(xs,item)),
            {'Induction':dict(variable='xs',names=['head','tail'],base=cases(equal(x,item)),step=step)})
        rows[name]=helper;helper_id=identity(semantic_entry(helper))
        ordered=lambda ys:op(sequence,'method:sort',ys)
        inserted=count(insert(head,ordered(tail)),item);incremented=plus(delta(head),count(ordered(tail),item))
        step={'Trans':dict(middle=inserted,left='Normalize',right={'Trans':dict(middle=incremented,left={'Use':dict(law=helper_id,arguments=dict(xs=ordered(tail),x=head,item=item),premises=[])},right=cases(equal(head,item)))})}
        name='bags/sort-occurrences-'+ty.lower()
        root=law(dict(xs=sequence,item=scalar),count(ordered(xs),item),count(xs,item),
            {'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step=step)},dependencies=[helper_id])
        rows[name]=root;root_id=identity(semantic_entry(root));observed=var(scalar,'observed')
        from_function=lam(scalar,count(ordered(xs),bound(scalar,0)));to_function=lam(scalar,count(xs,bound(scalar,0)))
        rows['bags/sort-observer-'+ty.lower()]=law(dict(xs=sequence),from_function,to_function,
            {'Forall':dict(parameter='observed',body={'Use':dict(law=root_id,arguments=dict(xs=xs,item=observed),premises=[])})},dependencies=[root_id])
    return rows
