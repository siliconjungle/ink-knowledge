"""Checked shared traversals for all nine ordered insert/replace/remove pairs.

The split predicate changes cost only. Both paths prove the same sequential
result; reads and argument computations remain at their original term positions.
"""
from producers.action_replacement import var,call,cons,convert
from producers.point_delta import match,sub,binary,choice
from producers.equational import Tactic,factor


def build(layout,objects,add,fun,law,rules,opaque):
    table,n=layout['table'],layout['roles'];T={'Data':n['tree']}
    row=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    key_sort=objects[table['get']]['payload']['declaration']['Function']['params'][1][1]
    tree=var('group_tree');first,second=var('group_first'),var('group_second')
    less=lambda a,b:call(n['key_less'],[a,b])
    negate=lambda p:choice(p,{'Bool':False},{'Bool':True})
    within=lambda k:binary('&&',negate(less(k,call(n['low'],[tree]))),negate(less(call(n['high'],[tree]),k)))
    eligible=fun([['group_tree',T],['group_first',key_sort],['group_second',key_sort]],'Bool',binary('&&',within(first),within(second)))
    opaque.extend([eligible,n['branch']])
    rules.extend(n[k] for k in ['decode_branch','decode_choice','repair_choice','branch_preserves_metadata','encode_preserves_rows','encode_preserves_metadata','replace_append','remove_append'])
    from producers.inserting_groups import prepare,body as inserting_body
    inserting=prepare(layout,objects,add,fun,law,rules,opaque)
    constructors=objects[n['tree']]['payload']['declaration']['Datatype']['constructors'];pairs={};proofs={}
    for op1 in ['replace','remove','insert']:
        for op2 in ['replace','remove','insert']:
            rest=[['group_first',key_sort]]+([['group_value_first',row]] if op1!='remove' else [])+[['group_second',key_sort]]+([['group_value_second',row]] if op2!='remove' else [])
            args=[var(x) for x,_ in rest];args1=[first]+([var('group_value_first')] if op1!='remove' else []);args2=[second]+([var('group_value_second')] if op2!='remove' else [])
            rawseq=lambda t:call(n[op2],[call(n[op1],[t,*args1]),*args2])
            fresh=lambda t:call(n['repair'],[t]);decode=lambda t:call(n['decode'],[t]);source=lambda t:call(table[op2],[call(table[op1],[t,*args1]),*args2])
            sequential=fun([['group_tree',T],*rest],T,rawseq(tree))
            seq=lambda t:call(sequential,[t,*args])
            seq_laws=[]
            for aa,zz in [(decode(seq(fresh(tree))),source(decode(tree))),(fresh(seq(fresh(tree))),seq(fresh(tree)))]:
                tactic=Tactic(objects,rules,opaque=opaque,prove_conditions=True)
                ident=law([['group_tree',T],*rest],aa,zz,tactic.prove(aa,zz))
                seq_laws.append((aa,zz,ident))
            opaque.append(sequential)
            rules.extend(ident for _,_,ident in seq_laws)
            from producers.action_replacement import trans
            from producers.point_delta import lift
            for label,(_,_,ident) in zip(['rows','metadata'],seq_laws):
                aa=decode(seq(tree)) if label=='rows' else fresh(seq(tree));zz=source(decode(tree)) if label=='rows' else seq(tree)
                context=decode(seq(var('delta_hole'))) if label=='rows' else fresh(seq(var('delta_hole')))
                p=trans(lift({'Sym':{'Hypothesis':0}},context),{'Use':dict(theorem=ident,arguments=[tree,*args],premises=[])})
                if label=='metadata':p=trans(p,lift({'Hypothesis':0},seq(var('delta_hole'))))
                rules.append(law([['group_tree',T],*rest],aa,zz,p,[{'from':fresh(tree),'to':tree}]))
            bs=['group_left','group_right','group_low','group_high','group_sum','group_count','group_height']
            joined=call(n['branch'],[{'SelfCall':[var('group_left'),*args]},{'SelfCall':[var('group_right'),*args]}])
            body=choice(call(eligible,[tree,first,second]),match(tree,[([],seq(tree)),(['group_key','group_value'],seq(tree)),(bs,joined)]),seq(tree))
            if 'insert' in [op1,op2]:body=inserting_body(inserting,layout,op1,op2,args,args1,args2,bs,seq)
            grouped=fun([['group_tree',T],*rest],T,body,0)
            left,right=var('group_left'),var('group_right');parent=call(n['branch'],[left,right])
            branch_a=call(grouped,[parent,*args])
            branch_z=choice(call(eligible,[parent,first,second]),call(n['branch'],[call(grouped,[left,*args]),call(grouped,[right,*args])]),seq(parent))
            if 'insert' in [op1,op2]:
                def recursive_calls(t):
                    if isinstance(t,list):return [recursive_calls(x) for x in t]
                    if not isinstance(t,dict):return t
                    if 'SelfCall' in t:return call(grouped,t['SelfCall'])
                    return {k:recursive_calls(v) for k,v in t.items()}
                branch_z=recursive_calls(body['Match']['branches'][2]['body'])
            rules.append(law([['group_left',T],['group_right',T],*rest],branch_a,branch_z,convert(branch_a,branch_z)))
            batch=lambda t:call(grouped,[t,*args])
            for label,a,z in [('rows',decode(batch(fresh(tree))),source(decode(tree))),('metadata',fresh(batch(fresh(tree))),batch(fresh(tree)))]:
                cases=[]
                tactic=Tactic(objects,rules,opaque=opaque,prove_conditions=True)
                for i,c in enumerate(constructors):
                    import os,sys
                    if os.environ.get('INK_PRODUCER_TRACE'):print('grouped',op1,op2,label,i,file=sys.stderr,flush=True)
                    ns=[] if i==0 else ['group_key','group_value'] if i==1 else bs
                    bound=cons(n['tree'],i,[var(x) for x in ns]);env={'group_tree':bound}
                    hypotheses=[(sub(a,{'group_tree':var(child)}),sub(z,{'group_tree':var(child)}),j) for j,child in enumerate(bs[:2])] if i==2 else []
                    proof=tactic.prove(sub(a,env),sub(z,env),hypotheses=hypotheses)
                    sorts=[T if f=='SelfType' else f for f in c['fields']];params=[*zip(ns,sorts),*rest]
                    conditions=[dict(zip(['from','to'],[x,y])) for x,y,_ in hypotheses]
                    proof=factor(proof,params,conditions,add,objects);cases.append(dict(bindings=ns,proof=proof))
                ident=law([['group_tree',T],*rest],a,z,{'Induction':dict(variable='group_tree',**{'from':a,'to':z},cases=cases)})
                proofs[op1+'-'+op2+'/'+label]=ident
                # Expose the bridge for arbitrary valid roots, rather than insert
                # a repair traversal into executable actions.
                valid={'from':fresh(tree),'to':tree}
                from producers.action_replacement import trans
                from producers.point_delta import lift
                aa=decode(batch(tree)) if label=='rows' else fresh(batch(tree));zz=source(decode(tree)) if label=='rows' else batch(tree)
                context=decode(batch(var('delta_hole'))) if label=='rows' else fresh(batch(var('delta_hole')))
                p=trans(lift({'Sym':{'Hypothesis':0}},context),{'Use':dict(theorem=ident,arguments=[tree,*args],premises=[])})
                if label=='metadata':p=trans(p,lift({'Hypothesis':0},batch(var('delta_hole'))))
                rules.append(law([['group_tree',T],*rest],aa,zz,p,[valid]))
            pairs[op1,op2]=grouped
            proofs[op1+'-'+op2+'/execute']=grouped
    layout['grouped_proofs']=proofs
    return pairs
