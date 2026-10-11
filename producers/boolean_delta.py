"""Generic any/all insert maintenance with checked refresh fallbacks.

The query must prove its decomposition as OR or AND over row contributions.
No source spelling, unique keys or bounded count is a proof assumption.
"""
from producers.action_replacement import var, call, cons, trans
from producers.point_delta import normal, sub, binary, choice, match, lift
from producers.equational import Tactic, factor
from producers.boolean_algebra import Tactic as Boolean


def setup(model,cache,add,objects):
    if len(model['tables'])!=1:raise ValueError('Boolean aggregate authoring supports one table')
    table=model['tables'][0];d=table['datatype'];L={'Data':d}
    binding=cache['case']['bindings'][0];query=cache['case']['normal']['Construct']['arguments'][0]
    q=lambda r:sub(query,{binding:r})
    nil=cons(d,0,[]);identity=normal(q(nil),objects)
    if identity not in [{'Bool':False},{'Bool':True}]:raise ValueError('query needs a Boolean fold identity')
    operation='&&' if identity['Bool'] else '||'
    value_sort=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    original_add=add
    carriers=[i for i,x in model['objects'].items() if 'Datatype' in x['payload'].get('declaration',{})]
    add=lambda declaration:original_add(declaration,carriers)
    def fun(params,result,body,recursive=None):return add({'Function':dict(params=params,result=result,body=body,recursive=recursive)})
    def theorem(params,a,z,proof):return add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
    def induction(a,z,base,step):return {'Induction':dict(variable='boolean_rows',**{'from':a,'to':z},cases=[dict(bindings=[],proof=base),dict(bindings=['boolean_key','boolean_value','boolean_tail'],proof=step)])}
    rows,key,value,tail,target,new=map(var,['boolean_rows','boolean_key','boolean_value','boolean_tail','boolean_target','boolean_new'])
    head=cons(d,1,[key,value,tail])
    contribution=fun([['boolean_key','U64'],['boolean_value',value_sort]],'Bool',q(cons(d,1,[key,value,nil])))
    contrib=lambda k,v:call(contribution,[k,v])
    fold=fun([['boolean_rows',L]],'Bool',match(rows,[([],identity),(['boolean_key','boolean_value','boolean_tail'],binary(operation,contrib(key,value),{'SelfCall':[tail]}))]),0)
    total=lambda r:call(fold,[r])
    boolean=Boolean(add);tactic=Tactic(objects,algebra=boolean.prove)
    a=q(rows);z=total(rows)
    fusion=theorem([['boolean_rows',L]],a,z,induction(a,z,tactic.prove(q(nil),total(nil)),tactic.prove(q(head),total(head),[(q(tail),total(tail),0)])))
    changed=lambda r:call(table['insert'],[r,target,new])
    lhs=lambda r:total(changed(r));rhs=lambda r:binary(operation,total(r),contrib(target,new))
    params=[['boolean_rows',L],['boolean_target','U64'],['boolean_new',value_sort]]
    proof=tactic.prove(lhs(head),rhs(head),[(lhs(tail),rhs(tail),0)])
    proof=factor(proof,params[1:]+[['boolean_key','U64'],['boolean_value',value_sort],['boolean_tail',L]],[{'from':lhs(tail),'to':rhs(tail)}],add)
    law=theorem(params,lhs(rows),rhs(rows),induction(lhs(rows),rhs(rows),tactic.prove(lhs(nil),rhs(nil)),proof))
    a=q(changed(rows));z=binary(operation,q(rows),contrib(target,new))
    delta=theorem(params,a,z,trans({'Use':dict(theorem=fusion,arguments=[changed(rows)],premises=[])},
        {'Use':dict(theorem=law,arguments=[rows,target,new],premises=[])},
        {'Binary':dict(op=operation,left={'Sym':{'Use':dict(theorem=fusion,arguments=[rows],premises=[])}},right={'Refl':contrib(target,new)})}))
    def recipe(root,old,bindings):
        if root==var(bindings[0]):return old
        x=root.get('Call',{});args=x.get('arguments',[])
        if x.get('function')==table['insert']:return binary(operation,recipe(args[0],old,bindings),contrib(args[1],args[2]))
        return sub(query,{binding:root})
    def action(sa):
        def predict(t):
            if 'If' in t:
                x=t['If'];yes,no=predict(x['on_true']),predict(x['on_false'])
                return yes if yes==no else choice(x['condition'],yes,no)
            x=t['Construct'];args=x['arguments']
            if x['constructor']!=0 or args[1]!={'Bool':True}:return var('cached_reply')
            return recipe(args[3]['Construct']['arguments'][0],var('cached_reply'),sa['case']['bindings'])
        return predict(sa['case']['normal'])
    def equality(root,bindings):
        if root==var(bindings[0]):return {'Refl':sub(query,{binding:root})}
        x=root.get('Call',{});args=x.get('arguments',[])
        if x.get('function')!=table['insert']:return {'Refl':sub(query,{binding:root})}
        return trans({'Use':dict(theorem=delta,arguments=args,premises=[])},lift(equality(args[0],bindings),binary(operation,var('delta_hole'),contrib(args[1],args[2]))))
    return dict(action=action,recipe=recipe,equality=equality,index=0)
