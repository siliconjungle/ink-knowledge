"""Propose one checked key index for a batch of ordered membership queries.

U32/U64 map and filter callbacks retain their exact values and output order.
Construction, memory and lookup costs still require whole-workload selection.
This does not retain an index across separate public calls or add a core rule.
"""
from ink_knowledge import identity,semantic_entry
from producers.semantic_laws import value,var,bound,lam,op,law,term
from producers.owned_fold_contracts import closed
from producers.definition_context28 import bind
from ink_planner.semantic_search import positions,children,shift
from producers.beta_specialization15 import beta_normalize

def specialize(subject,core):
    boolean=value('Bool');false=term(boolean,{'Bool':False});true=term(boolean,{'Bool':True})
    def operation(t):return t['node'].get('Op')if isinstance(t['node'],dict)else None
    def free(t,params):
        n=t['node']
        if isinstance(n,dict)and'Free'in n:params[n['Free']]=t['sort']
        for c in children(t):free(c,params)
    def apply(f,x):return op(f['sort']['Arrow'][1],'apply',f,x)
    def trans(m,a,b):return {'Trans':dict(middle=m,left=a,right=b)}
    out=[];helpers={}
    for function,root in sorted(subject['functions'].items()):
        for path,source in positions(root):
            outer=operation(source)
            if not outer or outer[0]not in ['method:map','method:filter']or not closed(source):continue
            queries,callback=outer[1]
            if not isinstance(callback['node'],dict)or'Lambda'not in callback['node']:continue
            body=callback['node']['Lambda'];member=operation(body)
            # First domain: membership itself is the mapped value or filter.
            # Arbitrary surrounding expressions can later use ordinary congruence.
            if not member or member[0]!='call:foldr'or len(member[1])!=3:continue
            table,seed,scan=member[1]
            if seed!=false:continue
            try:scan_body=scan['node']['Lambda']['node']['Lambda']
            except(KeyError,TypeError):continue
            disjunction=operation(scan_body)
            if not disjunction or disjunction[0]!='binary:||'or disjunction[1][1]!=bound(boolean,0):continue
            equality=operation(disjunction[1][0])
            if not equality or equality[0]!='binary:==':continue
            captured,element=equality[1]
            if element!=bound(element['sort'],1):continue
            def independent(t,depth=0):
                n=t['node']
                if isinstance(n,dict)and'Bound'in n and depth<=n['Bound']<depth+2:return False
                return all(independent(c,depth+int(isinstance(n,dict)and'Lambda'in n))for c in children(t))
            if not independent(captured):continue
            key=shift(captured,-2);key_type=key['sort'].get('Value')if isinstance(key['sort'],dict)else None
            if key_type not in ['U32','U64']or not closed(table):continue
            scalar=value(key_type);sequence=value({'List':key_type});index_type=value({'Map':[key_type,'Bool']})
            def index(xs):
                step=lam(scalar,lam(index_type,op(index_type,'method:set',bound(index_type,0),bound(scalar,1),true)))
                return op(index_type,'call:foldr',xs,op(index_type,'local:map-empty'),step)
            def contains(xs,key):
                step=lam(scalar,lam(boolean,op(boolean,'binary:||',op(boolean,'binary:==',shift(key,2),bound(scalar,1)),bound(boolean,0))))
                return op(boolean,'call:foldr',xs,false,step)
            if key_type not in helpers:
                xs,item=var(sequence,'indexed_items'),var(scalar,'indexed_key')
                head=var(scalar,'indexed_head');tail=var(sequence,'indexed_tail')
                recurse=trans(contains(tail,item),'Normalize',trans(op(boolean,'method:contains',index(tail),item),{'Hypothesis':0},'Normalize'))
                helper=law({'indexed_items':sequence,'indexed_key':scalar},
                    contains(xs,item),op(boolean,'method:contains',index(xs),item),
                    {'Induction':dict(variable='indexed_items',names=['indexed_head','indexed_tail'],base='Normalize',
                        step={'Cases':dict(condition=op(boolean,'binary:==',item,head),on_true='Normalize',on_false=recurse)})})
                helper=bind(helper,core,subject);ident=identity(semantic_entry(helper));helpers[key_type]=(ident,helper)
                out.append(('index_membership_'+key_type,helper))
            ident,_=helpers[key_type]
            params={};free(source,params)
            parameter='indexed_query'
            while parameter in params:parameter+='_' 
            argument=var(callback['sort']['Arrow'][0],parameter)
            query=beta_normalize(apply(callback,argument))
            table0=table;key0=beta_normalize(apply(lam(callback['sort']['Arrow'][0],key),argument))
            direct_callback=lam(callback['sort']['Arrow'][0],op(boolean,'method:contains',index(table),key))
            middle=op(source['sort'],outer[0],queries,direct_callback)
            held=lam(callback['sort']['Arrow'][0],op(boolean,'method:contains',bound(index_type,1),shift(key,1,1)))
            abstraction=lam(index_type,op(source['sort'],outer[0],shift(queries,1),held))
            # table was observed under the callback; it has no escaping bound variables.
            target=apply(abstraction,index(table))
            use={'Use':dict(law=ident,arguments={'indexed_items':table0,'indexed_key':key0},premises=[])}
            point=trans(query,'Normalize',trans(op(boolean,'method:contains',index(table0),key0),use,'Normalize'))
            proof=trans(middle,{'Congruence':['Normalize',{'Forall':dict(parameter=parameter,body=point)}]},'Normalize')
            out.append((function+'_indexed_lookup_'+'_'.join(map(str,path)),bind(law(params,source,target,proof,dependencies=[ident]),core,subject)))
            if len(out)>=64:return out
    return out
