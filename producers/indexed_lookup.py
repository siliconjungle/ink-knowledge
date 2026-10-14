"""Propose shared indexes for ordered batches of membership observations.

U32/U64 membership may appear inside records, conditions and nested callbacks.
Each independent key list gets one private index for the batch. Ordinary
Forall/Congruence/Use proofs preserve the complete callback result and order;
no source recogniser grants authority. Construction, memory and lookup costs
still require whole-workload selection. Indexes do not persist across calls.
"""
from ink_knowledge import identity,semantic_entry,canonical
from producers.semantic_laws import value,var,bound,lam,op,law,term
from producers.owned_fold_contracts import closed
from producers.definition_context28 import bind
from producers.contract_proofs import proof_semantics
from ink_planner.semantic_search import positions,children,shift,substitute,map_children
from producers.beta_specialization15 import instantiate_bound,free_parameters


def specialize(subject,core):
    boolean=value('Bool');false=term(boolean,{'Bool':False});true=term(boolean,{'Bool':True})
    def operation(t):return t['node'].get('Op')if isinstance(t['node'],dict)else None
    def apply(f,x):return op(f['sort']['Arrow'][1],'apply',f,x)
    def trans(m,a,b):return {'Trans':dict(middle=m,left=a,right=b)}
    def fresh(stem,used):
        while stem in used:stem+='_' 
        used.add(stem);return stem
    def independent(t,depth=0):
        n=t['node']
        if isinstance(n,dict)and'Bound'in n and depth<=n['Bound']<depth+2:return False
        return all(independent(c,depth+int(isinstance(n,dict)and'Lambda'in n))for c in children(t))
    def membership(t):
        member=operation(t)
        if not member or member[0]not in ['call:foldr','call:foldl']or len(member[1])!=3:return None
        table,seed,scan=member[1]
        if seed!=false or not closed(table):return None
        try:scan_body=scan['node']['Lambda']['node']['Lambda']
        except(KeyError,TypeError):return None
        disjunction=operation(scan_body)
        if not disjunction or disjunction[0]!='binary:||'or len(disjunction[1])!=2:return None
        for equality_term,acc in [disjunction[1],disjunction[1][::-1]]:
            if acc!=bound(boolean,0):continue
            equality=operation(equality_term)
            if not equality or equality[0]!='binary:=='or len(equality[1])!=2:continue
            for captured,element in [equality[1],equality[1][::-1]]:
                if element!=bound(element['sort'],1)or not independent(captured):continue
                key=shift(captured,-2);key_type=key['sort'].get('Value')if isinstance(key['sort'],dict)else None
                if key_type not in ['U32','U64']or table['sort']!=value({'List':key_type}):continue
                return table,key,key_type,member[0]
        return None
    def index(xs,key_type):
        scalar=value(key_type);index_type=value({'Map':[key_type,'Bool']})
        step=lam(scalar,lam(index_type,op(index_type,'method:set',bound(index_type,0),bound(scalar,1),true)))
        return op(index_type,'call:foldr',xs,op(index_type,'local:map-empty'),step)
    def contains(xs,key,direction='call:foldr',seed=None):
        scalar=key['sort']
        predicate=op(boolean,'binary:==',shift(key,2),bound(scalar,1));found=bound(boolean,0)
        step=lam(scalar,lam(boolean,op(boolean,'binary:||',*([found,predicate]if direction=='call:foldl'else[predicate,found]))))
        return op(boolean,direction,xs,false if seed is None else seed,step)
    out=[];helpers={}
    def helper(key_type,direction):
        signature=(key_type,direction)
        if signature not in helpers:
            scalar=value(key_type);sequence=value({'List':key_type})
            xs,item=var(sequence,'indexed_items'),var(scalar,'indexed_key')
            head=var(scalar,'indexed_head');tail=var(sequence,'indexed_tail')
            recurse=trans(contains(tail,item),'Normalize',trans(op(boolean,'method:contains',index(tail,key_type),item),{'Hypothesis':0},'Normalize'))
            proof=law({'indexed_items':sequence,'indexed_key':scalar},
                contains(xs,item),op(boolean,'method:contains',index(xs,key_type),item),
                {'Induction':dict(variable='indexed_items',names=['indexed_head','indexed_tail'],base='Normalize',
                    step={'Cases':dict(condition=op(boolean,'binary:==',item,head),on_true='Normalize',on_false=recurse)})})
            name='index_membership_'+key_type
            if direction=='call:foldl':
                initial=var(boolean,'indexed_initial')
                next_seed=op(boolean,'binary:||',initial,op(boolean,'binary:==',item,head))
                next_scan=contains(tail,item,direction,next_seed)
                next_result=op(boolean,'binary:||',op(boolean,'method:contains',index(tail,key_type),item),next_seed)
                branches='Normalize'
                for condition in [op(boolean,'method:contains',index(tail,key_type),item),op(boolean,'binary:==',item,head),initial]:
                    branches={'Cases':dict(condition=condition,on_true=branches,on_false=branches)}
                step=trans(next_scan,'Normalize',trans(next_result,
                    {'GeneralizedHypothesis':dict(index=0,arguments={'indexed_initial':next_seed})},branches))
                proof=law({'indexed_items':sequence,'indexed_key':scalar,'indexed_initial':boolean},
                    contains(xs,item,direction,initial),op(boolean,'binary:||',op(boolean,'method:contains',index(xs,key_type),item),initial),
                    {'GeneralizedInduction':dict(variable='indexed_items',generalize=['indexed_initial'],names=['indexed_head','indexed_tail'],base='Normalize',step=step)})
                name='index_membership_left_'+key_type
            proof=bind(proof,core,subject);ident=identity(semantic_entry(proof));helpers[signature]=(ident,proof)
            out.append((name,proof))
        return helpers[signature][0]
    for function,root in sorted(subject['functions'].items()):
        for path,source in positions(root):
            outer=operation(source)
            if not outer or outer[0]not in ['method:map','method:filter']or not closed(source):continue
            queries,callback=outer[1]
            if not isinstance(callback['node'],dict)or'Lambda'not in callback['node']:continue
            params=free_parameters(source);used=set(params);groups={};budget=[20_000];occurrences=[0]
            def rewrite(t):
                budget[0]-=1
                if budget[0]<0:raise ValueError('indexed callback discovery budget')
                match=membership(t)
                if match:
                    table,key,key_type,direction=match;signature=canonical(table)
                    if signature not in groups:
                        if len(groups)>=4:raise ValueError('indexed callback group budget')
                        sort=value({'Map':[key_type,'Bool']})
                        groups[signature]=(fresh('indexed_table',used),sort,table,key_type)
                    name,sort,_,_=groups[signature]
                    occurrences[0]+=1
                    if occurrences[0]>128:raise ValueError('indexed callback occurrence budget')
                    return op(boolean,'method:contains',var(sort,name),key)
                return map_children(t,rewrite)
            try:held_callback=rewrite(callback)
            except(ValueError,RecursionError):continue
            if not groups:continue
            direct_callback=substitute(held_callback,{name:index(table,kind)for name,_,table,kind in groups.values()})
            middle=op(source['sort'],outer[0],queries,direct_callback)
            target=op(source['sort'],outer[0],queries,held_callback)
            for name,sort,table,kind in reversed(list(groups.values())):
                target=apply(lam(sort,substitute(target,{name:bound(sort,0)})),index(table,kind))
            dependencies=set();proof_budget=[20_000]
            def prove(before,after):
                proof_budget[0]-=1
                if proof_budget[0]<0:raise ValueError('indexed callback proof budget')
                if before==after:return 'Normalize'
                match=membership(before)
                if match:
                    table,key,kind,direction=match;ident=helper(kind,direction);dependencies.add(ident)
                    expected=op(boolean,'method:contains',index(table,kind),key)
                    if after!=expected:raise ValueError('indexed callback endpoint mismatch')
                    use={'Use':dict(law=ident,arguments={'indexed_items':table,'indexed_key':key},premises=[])}
                    canonical_scan=contains(table,key,direction)
                    if direction=='call:foldl':
                        use['Use']['arguments']['indexed_initial']=false
                        use=trans(op(boolean,'binary:||',expected,false),use,'Normalize')
                    if before==canonical_scan:return use
                    item_name=fresh('indexed_item',used);found_name=fresh('indexed_found',used)
                    branches={'Cases':dict(condition=var(boolean,found_name),on_true='Normalize',on_false='Normalize')}
                    callback_proof={'Forall':dict(parameter=item_name,body={'Forall':dict(parameter=found_name,
                        body={'Order':dict(atoms=[key,var(key['sort'],item_name)],body=branches)})})}
                    alignment={'Congruence':['Normalize','Normalize',callback_proof]}
                    return trans(canonical_scan,alignment,use)
                if isinstance(before['node'],dict)and'Lambda'in before['node']:
                    parameter=fresh('indexed_query',used);argument=var(before['sort']['Arrow'][0],parameter)
                    return {'Forall':dict(parameter=parameter,body=prove(
                        instantiate_bound(before['node']['Lambda'],argument),
                        instantiate_bound(after['node']['Lambda'],argument)))}
                return {'Congruence':[prove(a,b)for a,b in zip(children(before),children(after))]}
            try:proof=trans(middle,{'Congruence':['Normalize',prove(callback,direct_callback)]},'Normalize')
            except(ValueError,RecursionError):continue
            candidate=law(params,source,target,proof,dependencies=sorted(dependencies))
            candidate['semantics']=proof_semantics(proof)
            out.append((function+'_indexed_lookup_'+'_'.join(map(str,path)),bind(candidate,core,subject)))
            if len(out)>=64:return out
    return out
