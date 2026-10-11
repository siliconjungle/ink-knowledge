"""Untrusted universal early termination laws. Ordinary induction, no compiler matcher."""
from pathlib import Path
import json
from ink_knowledge import Store, canonical, semantic_entry, identity
if __package__ in (None, ""):
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from producers.semantic_laws import value,arrow,term,var,bound,lam,op,law


def named_laws():
    rows=[]
    for t in ('U32','I32','U64','F32','Bool','Int','String','Unit'):
        s,b=value(t),value('Bool');ls=value({'List':t})
        xs,z=var(ls,'xs'),var(s,'z');p,f=var(arrow(s,b),'p'),var(arrow(s,s),'f')
        item,acc=bound(s,1),bound(s,0)
        pred=op(b,'apply',p,item);mapped=op(s,'apply',f,item)
        step=lam(s,lam(s,op(s,'call:choose',pred,mapped,acc)))
        stop=lam(s,lam(s,pred))
        source=op(s,'call:foldr',xs,z,step)
        target=op(s,'call:fold_until',xs,z,stop,step)
        proof={'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step={'Cases':dict(condition=op(b,'apply',p,var(s,'head')),on_false='Normalize',on_true='Normalize')})}
        rows.append(('fold_first_replacement_'+t.lower(),law(dict(xs=ls,z=s,p=p['sort'],f=f['sort']),source,target,proof)))
    return rows


def publish(root):
    rows=named_laws();names={n:identity(semantic_entry(l))for n,l in rows}
    st=Store.publish(root,[semantic_entry(l)for _,l in rows],names)
    (Path(root)/'view.json').write_bytes(canonical(st.bundle(sorted(names.values())))+b'\n')
    return st

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('output');a=p.parse_args();st=publish(a.output);print(st.snapshot_id)


def specialize(subject, core=None):
    """Propose checked decision-tree laws over arbitrary item/result carriers.

    This recogniser is untrusted database tooling. Every proposal contains a full
    induction/case proof; no compiler or target accepts it without checking.
    Accumulator-dependent conditions/results are rejected, including hidden uses
    under local binders. Only closed lexical sites are considered by this producer.
    """
    from ink_planner.semantic_search import children,positions,shift
    import copy
    def uses_acc(t,depth=0):
        n=t['node']
        return (isinstance(n,dict)and n.get('Bound')==depth)or any(uses_acc(c,depth+int('Lambda' in n))for c in children(t))
    def replace_item(t,head,depth=0):
        n=t['node']
        if isinstance(n,dict)and 'Bound' in n:
            i=n['Bound']
            if i==depth:raise ValueError('accumulator dependence')
            if i==depth+1:return shift(head,depth)
            if i>depth+1:raise ValueError('outer binder requires explicit abstraction')
            return copy.deepcopy(t)
        t=copy.deepcopy(t)
        from ink_planner.semantic_search import set_child
        for i,c in enumerate(children(t)):t=set_child(t,i,replace_item(c,head,depth+int('Lambda' in n)))
        return t
    def free_params(t,out):
        n=t['node']
        if isinstance(n,dict)and 'Free' in n:out[n['Free']]=t['sort']
        for c in children(t):free_params(c,out)
    rows=[];bases={}
    for name,root in sorted(subject['functions'].items()):
        for path,source in positions(root):
            n=source['node']
            if not isinstance(n,dict)or n.get('Op',[None])[0]!='call:foldr':continue
            xs,z,step=n['Op'][1]
            if not isinstance(xs['sort'].get('Value'),dict)or 'List' not in xs['sort']['Value']:continue
            try:body=step['node']['Lambda']['node']['Lambda']
            except(KeyError,TypeError):continue
            b=value('Bool');conditions=[]
            def mask(t):
                node=t['node']
                if isinstance(node,dict)and node.get('Bound')==0:return term(b,{'Bool':False})
                if isinstance(node,dict)and node.get('Op',[None])[0]=='call:choose':
                    condition,yes,no=node['Op'][1]
                    if uses_acc(condition):raise ValueError('accumulator-dependent condition')
                    conditions.append(condition)
                    return op(b,'call:choose',condition,mask(yes),mask(no))
                if uses_acc(t):raise ValueError('accumulator-dependent replacement')
                return term(b,{'Bool':True})
            try:
                stop_body=mask(body)
                item_sort=step['sort']['Arrow'][0];acc_sort=source['sort']
                def closed(t,depth=0):
                    node=t['node']
                    return not(isinstance(node,dict)and 'Bound' in node and node['Bound']>=depth)and all(closed(c,depth+int('Lambda' in node))for c in children(t))
                if not closed(source):continue
                params={};free_params(source,params)
                fresh=lambda stem:next(stem+str(i)for i in range(4097)if stem+str(i)not in params)
                seq,head,tail=fresh('__xs'),fresh('__head'),fresh('__tail')
                params[seq]=xs['sort'];input_xs=var(xs['sort'],seq)
                generic=op(acc_sort,'call:foldr',input_xs,z,step)
                target=op(acc_sort,'call:fold_until',input_xs,z,lam(item_sort,lam(acc_sort,stop_body)),step)
                proof='Normalize'
                # Cases enumerate branch facts, preserving exact scalar semantics.
                unique=[]
                for c in conditions:
                    c=replace_item(c,var(item_sort,head))
                    if c not in unique:unique.append(c)
                if len(unique)>8:continue # producer/search budget, never authority
                for c in reversed(unique):proof={'Cases':dict(condition=c,on_false=proof,on_true=proof)}
                proof={'Induction':dict(variable=seq,names=[head,tail],base='Normalize',step=proof)}
                params={};free_params(generic,params)
                # Compose a universal law rather than asking source-specific
                # normalization to reason about the internals of captured work.
                body_node=body['node']
                if isinstance(body_node,dict)and body_node.get('Op',[None])[0]=='call:choose':
                    cond,replacement,otherwise=body_node['Op'][1]
                    if otherwise['node']=={'Bound':0}and not uses_acc(replacement):
                        isort,rsort=item_sort,acc_sort;list_sort=xs['sort']
                        vx,vz=var(list_sort,'xs'),var(rsort,'z');ps,fs=arrow(isort,b),arrow(isort,rsort)
                        vp,vf=var(ps,'p'),var(fs,'f');ix,ia=bound(isort,1),bound(rsort,0)
                        pred=op(b,'apply',vp,ix);val=op(rsort,'apply',vf,ix)
                        callback=lam(isort,lam(rsort,op(rsort,'call:choose',pred,val,ia)))
                        stop=lam(isort,lam(rsort,op(b,'call:choose',pred,term(b,{'Bool':True}),term(b,{'Bool':False}))))
                        base=law(dict(xs=list_sort,z=rsort,p=ps,f=fs),op(rsort,'call:foldr',vx,vz,callback),op(rsort,'call:fold_until',vx,vz,stop,callback),{'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step={'Cases':dict(condition=op(b,'apply',vp,var(isort,'head')),on_false='Normalize',on_true='Normalize')})})
                        bid=identity(semantic_entry(base));bases[bid]=('generic_early_exit_'+bid[:12],base)
                        from ink_planner.semantic_search import substitute
                        arguments=dict(xs=input_xs,z=z,p=lam(isort,shift(cond,-1)),f=lam(isort,shift(replacement,-1)))
                        middle_from=substitute(base['from'],arguments);middle_to=substitute(base['to'],arguments)
                        use={'Use':dict(law=bid,arguments=dict(sorted(arguments.items())),premises=[])}
                        proof={'Trans':dict(middle=middle_from,left='Normalize',right={'Trans':dict(middle=middle_to,left=use,right='Normalize')})}
                        proposal=law(params,generic,target,proof,dependencies=[bid])
                    else:proposal=law(params,generic,target,proof)
                else:proposal=law(params,generic,target,proof)
                rows.append((name+'_'+'_'.join(map(str,path))+'_early_exit',proposal))
            except(ValueError,KeyError,TypeError):continue
    return list(bases.values())+rows
