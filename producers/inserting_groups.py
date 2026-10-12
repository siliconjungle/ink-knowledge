"""Ordinary routing and metadata laws for insertion-containing edit pairs."""
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import match,sub,binary,choice
from producers.key_order import Order
from producers.equational import Tactic,factor


def prepare(layout,objects,add,fun,law,rules,opaque):
    table,n=layout['table'],layout['roles'];T={'Data':n['tree']};R={'Data':table['datatype']}
    source_get=objects[table['get']]['payload']['declaration']['Function'];K=source_get['params'][1][1]
    row=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    order=Order.__new__(Order);order.objects=objects;order.add=add;order.sort=K;order.kind=table.get('key_type','U64');order.less_id=n['key_less'];order.equal_id=n['key_equal'];order.cache={}
    lt=order.less;hi=lambda t:call(n['high'],[t]);lo=lambda t:call(n['low'],[t]);branch=lambda l,r:call(n['branch'],[l,r]);fix=lambda t:call(n['repair'],[t])
    bottom_query=var('bottom_query');bottom_goal=lt(bottom_query,hi(cons(n['tree'],0,[])))
    bottom_law=law([['bottom_query',K]],bottom_goal,{'Bool':False},order.prove([['bottom_query',K]],bottom_goal,{'Bool':False}))
    f,s=var('group_first'),var('group_second');left,right=var('group_left'),var('group_right')
    def use(i,args,premises=()):return {'Use':dict(theorem=i,arguments=args,premises=list(premises))}
    # Inspect cached bounds without unfolding every other parent metadata field.
    cached_rules=[]
    for field,end in [('high',order.maximum(hi(left),hi(right))),('low',order.minimum(lo(left),lo(right)))]:
        a=call(n[field],[branch(left,right)]);ident=law([['group_left',T],['group_right',T]],a,end,convert(a,end));rules.append(ident);cached_rules.append(ident)
    cached_rules.extend([n['below_maximum'],bottom_law]);rules.append(bottom_law)
    rules.extend(n[k] for k in ['balance_preserves_rows','balance_preserves_metadata','maximum_matches_rows','below_maximum','insert_append','greater_append'])
    opaque.append(n['balance'])
    # Inserting a key adds precisely its singleton contribution to the query
    # "does any row contain a greater key?", including arbitrary duplicates.
    xs=var('insert_rows');a,b,new=var('insert_first'),var('insert_query'),var('insert_value')
    gr=lambda r,k:call(n['greater_rows'],[r,k]);insert=lambda r:call(table['insert'],[r,a,new])
    either=lambda x,y:choice(x,{'Bool':True},y)
    aa,zz=gr(insert(xs),b),either(lt(b,a),gr(xs,b));bindings=['insert_head','insert_row','insert_tail'];bound=cons(table['datatype'],1,[var(v) for v in bindings]);nil=cons(table['datatype'],0,[])
    tactic=Tactic(objects,rules,opaque=opaque,prove_conditions=True)
    p={'Induction':dict(variable='insert_rows',**{'from':aa,'to':zz},cases=[dict(bindings=[],proof=tactic.prove(sub(aa,{'insert_rows':nil}),sub(zz,{'insert_rows':nil}))),dict(bindings=bindings,proof=tactic.prove(sub(aa,{'insert_rows':bound}),sub(zz,{'insert_rows':bound}),[(sub(aa,{'insert_rows':var('insert_tail')}),sub(zz,{'insert_rows':var('insert_tail')}),0)]))])}
    greater_insert_law=law([['insert_rows',R],['insert_first',K],['insert_query',K],['insert_value',row]],aa,zz,p);rules.append(greater_insert_law)
    aa,zz=gr(call(table['replace'],[xs,a,new]),b),gr(xs,b)
    tactic=Tactic(objects,rules,opaque=opaque,prove_conditions=True)
    p={'Induction':dict(variable='insert_rows',**{'from':aa,'to':zz},cases=[dict(bindings=[],proof=tactic.prove(sub(aa,{'insert_rows':nil}),sub(zz,{'insert_rows':nil}))),dict(bindings=bindings,proof=tactic.prove(sub(aa,{'insert_rows':bound}),sub(zz,{'insert_rows':bound}),[(sub(aa,{'insert_rows':var('insert_tail')}),sub(zz,{'insert_rows':var('insert_tail')}),0)]))])}
    rules.append(law([['insert_rows',R],['insert_first',K],['insert_query',K],['insert_value',row]],aa,zz,p))
    # A key inserted below the old maximum cannot make an outside second key
    # route into that subtree. This is a source-order theorem, not a hint.
    x,a,b=var('x'),var('a'),var('b');conditions=[{'from':lt(a,x),'to':{'Bool':True}},{'from':lt(b,x),'to':{'Bool':False}}]
    rules.append(law([['x',K],['a',K],['b',K]],lt(b,a),{'Bool':False},order.prove([['x',K],['a',K],['b',K]],lt(b,a),{'Bool':False},conditions),conditions))
    aa,zz=either(lt(b,a),lt(b,x)),lt(b,x);condition=[conditions[0]]
    stable_order=law([['x',K],['a',K],['b',K]],aa,zz,order.prove([['x',K],['a',K],['b',K]],aa,zz,condition),condition)
    route_tree,route_a,route_b,route_value=map(var,['route_tree','route_first','route_query','route_value'])
    decoded=call(n['decode'],[route_tree]);maximum=hi(fix(route_tree));aa,zz=gr(call(table['insert'],[decoded,route_a,route_value]),route_b),gr(decoded,route_b)
    from producers.point_delta import lift
    p=trans(use(greater_insert_law,[decoded,route_a,route_b,route_value]),lift({'Sym':use(n['maximum_matches_rows'],[route_tree,route_b])},either(lt(route_b,route_a),var('delta_hole'))),use(stable_order,[maximum,route_a,route_b],[{'Hypothesis':0}]),use(n['maximum_matches_rows'],[route_tree,route_b]))
    rules.insert(0,law([['route_tree',T],['route_first',K],['route_query',K],['route_value',row]],aa,zz,p,[{'from':lt(route_a,maximum),'to':{'Bool':True}}]))
    # A virtual greater-key query after removal avoids constructing intermediate
    # parents just to choose the insertion branch.
    tree=var('remove_tree');first,second=var('remove_key'),var('remove_query');outside=lambda t:binary('||',lt(first,lo(t)),lt(hi(t),first))
    ns=['remove_left','remove_right','remove_low','remove_high','remove_sum','remove_count','remove_height']
    body=choice(outside(tree),lt(second,hi(tree)),match(tree,[([],{'Bool':False}),(['remove_head','remove_value'],choice(order.equal(first,var('remove_head')),{'Bool':False},lt(second,var('remove_head')))),(ns,either({'SelfCall':[var('remove_left'),first,second]},{'SelfCall':[var('remove_right'),first,second]}))]))
    virtual=fun([['remove_tree',T],['remove_key',K],['remove_query',K]],'Bool',body,0);opaque.append(virtual)
    virtual_call=lambda t:call(virtual,[t,first,second]);remove=lambda t:call(n['remove'],[t,first]);parent=branch(left,right)
    operational=choice(outside(parent),lt(second,hi(parent)),either(virtual_call(left),virtual_call(right)))
    ident=law([['group_left',T],['group_right',T],['remove_key',K],['remove_query',K]],virtual_call(parent),operational,convert(virtual_call(parent),operational));rules.append(ident);cached_rules.append(ident)
    remove_parent=choice(outside(parent),parent,branch(remove(left),remove(right)))
    ident=law([['group_left',T],['group_right',T],['remove_key',K]],remove(parent),remove_parent,convert(remove(parent),remove_parent));rules.append(ident);cached_rules.append(ident)
    opaque.append(n['remove'])
    cached_opaque=[*opaque,n['key_less'],n['key_equal']]
    aa,zz=lt(second,hi(remove(fix(tree)))),virtual_call(fix(tree))
    constructors=objects[n['tree']]['payload']['declaration']['Datatype']['constructors'];cases=[]
    for i,c in enumerate(constructors):
        bindings=[] if i==0 else ['remove_head','remove_value'] if i==1 else ns
        value=cons(n['tree'],i,[var(v) for v in bindings]);hypotheses=[(sub(aa,{'remove_tree':var(child)}),sub(zz,{'remove_tree':var(child)}),j) for j,child in enumerate(ns[:2])] if i==2 else []
        # Explicit leaf operational identities keep the update opaque elsewhere.
        if i<2:
            r=remove(fix(value))
            from producers.point_delta import normal
            rr=normal(r,objects,opaque=[x for x in cached_opaque if x!=n['remove']])
            ident=law([['remove_key',K],*zip(bindings,[K,row] if i==1 else [])],r,rr,convert(r,rr));rules.append(ident);cached_rules.append(ident)
            v=virtual_call(fix(value));vv=normal(v,objects,opaque=[x for x in cached_opaque if x!=virtual]);ident=law([['remove_key',K],['remove_query',K],*zip(bindings,[K,row] if i==1 else [])],v,vv,convert(v,vv));rules.append(ident);cached_rules.append(ident)
        tactic=Tactic(objects,cached_rules,opaque=cached_opaque,prove_conditions=True)
        p=tactic.prove(sub(aa,{'remove_tree':value}),sub(zz,{'remove_tree':value}),hypotheses)
        params=[['remove_key',K],['remove_query',K],*zip(bindings,[T if s=='SelfType' else s for s in c['fields']])]
        p=factor(p,params,[dict(**{'from':x,'to':y}) for x,y,_ in hypotheses],add,objects);cases.append(dict(bindings=bindings,proof=p))
    cached=law([['remove_tree',T],['remove_key',K],['remove_query',K]],aa,zz,{'Induction':dict(variable='remove_tree',**{'from':aa,'to':zz},cases=cases)});rules.append(cached)
    # Relate the virtual route to the complete logical removal. Metadata validity
    # and row preservation are existing universal obligations.
    logical=lambda t:call(n['decode'],[t]);source_remove=call(table['remove'],[logical(tree),first]);changed=remove(fix(tree))
    goal=virtual_call(fix(tree));end=gr(source_remove,second)
    from producers.point_delta import lift
    p=trans({'Sym':use(cached,[tree,first,second])},{'Sym':lift(use(n['indexed_remove_preserves_metadata'],[tree,first]),lt(second,hi(var('delta_hole'))))},use(n['maximum_matches_rows'],[changed,second]),lift(use(n['indexed_remove_preserves_rows'],[tree,first]),gr(var('delta_hole'),second)))
    rules.append(law([['remove_tree',T],['remove_key',K],['remove_query',K]],goal,end,p))
    # Replace keeps the routing keys; insertion and removal cases use their own
    # checked virtual routes. The final balance preserves enumeration and caches.
    return dict(order=order,virtual=virtual)


def body(info,layout,op1,op2,args,args1,args2,bindings,seq):
    n=layout['roles'];lt=info['order'].less;left,right=var('group_left'),var('group_right');first,second=var('group_first'),var('group_second')
    apply=lambda op,t,aa:call(n[op],[t,*aa]);balanced=lambda l,r:call(n['balance'],[l,r])
    pair=lambda t:{'SelfCall':[t,*args]}
    route_first=lt(first,call(n['high'],[left]))
    route_second=call(info['virtual'],[left,first,second]) if op1=='remove' else lt(second,call(n['high'],[left]))
    if op1=='insert' and op2=='insert':
        changed=choice(route_first,choice(route_second,balanced(pair(left),right),balanced(apply(op1,left,args1),apply(op2,right,args2))),choice(route_second,balanced(apply(op2,left,args2),apply(op1,right,args1)),balanced(left,pair(right))))
    elif op1=='insert':
        changed=choice(route_first,balanced(pair(left),apply(op2,right,args2)),balanced(apply(op2,left,args2),pair(right)))
    else:
        changed=choice(route_second,balanced(pair(left),apply(op1,right,args1)),balanced(apply(op1,left,args1),pair(right)))
    T=var('group_tree')
    return match(T,[([],seq(T)),(['group_key','group_value'],seq(T)),(bindings,changed)])
