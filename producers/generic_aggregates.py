"""Typed, key-aware products of independently checked query monoids.

Names and row field spelling have no authority. A candidate query must prove its
empty/step decomposition. Other queries keep their exact compiled evaluation.
"""
import os,json
from pathlib import Path
from ink_knowledge import canonical
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import normal,sub,binary,match
from producers.cache_maintenance import variables
from producers.equational import Tactic
from producers.boolean_algebra import Tactic as Boolean
from producers.word_ring import Tactic as Word

def factory(model,table,add,objects):
    key_sort=objects[table['get']]['payload']['declaration']['Function']['params'][1][1];rows=table['datatype'];R={'Data':rows};row=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    nil=cons(rows,0,[]);xs,k,v,tail=map(var,['summary_rows','summary_key','summary_value','summary_tail'])
    word=Word(add,Path(os.environ.get('INK_COMPILER','target/debug/ink')).resolve());boolean=Boolean(add);algebra_cache={}
    def arithmetic(a,z):
        atoms=[]
        def abstract(t):
            if 'U64' in t:return t
            if 'Binary' in t and t['Binary']['op'] in ['+','-','*']:
                b=t['Binary'];return binary(b['op'],abstract(b['left']),abstract(b['right']))
            if t not in atoms:atoms.append(t)
            return var('summary_atom_'+str(atoms.index(t)))
        aa,zz=abstract(a),abstract(z);key=json.dumps([aa,zz],sort_keys=True)
        if key not in algebra_cache:
            p=word.prove(aa,zz);algebra_cache[key]=add({'Theorem':dict(params=[['summary_atom_'+str(i),'U64'] for i in range(len(atoms))],conditions=[],**{'from':aa,'to':zz},proof=p)})
        return {'Use':dict(theorem=algebra_cache[key],arguments=atoms,premises=[])}
    def fun(params,result,body,recursive=None):return add({'Function':dict(params=params,result=result,body=body,recursive=recursive)})
    def law(params,a,z,p):return add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=p)})
    def terms(t):
        if isinstance(t,dict):
            if any(k in t for k in ['Call','Binary','If']):yield t
            for v in t.values():yield from terms(v)
        elif isinstance(t,list):
            for v in t:yield from terms(v)
    def result_sort(t):
        if 'Call' in t:return objects[t['Call']['function']]['payload']['declaration']['Function']['result']
        if 'Binary' in t:
            op=t['Binary']['op'];return 'U64' if op in ['+','-','*','&','quot','rem','f32:+','f32:-','f32:*','f32:neg'] else 'Bool'
        if 'If' in t:return result_sort(t['If']['on_true'])
        if 'Bool' in t:return 'Bool'
        if 'U64' in t:return 'U64'
        return None
    queries=[];candidates=[];seen=set()
    for name,action in sorted(model['actions'].items()):
        for q in terms(action['case']['normal']):
            marker=canonical(q)
            if marker not in seen:seen.add(marker);candidates.append((name,action,q))
    for name,action,q in candidates:
        observed=q;modular=None
        free=variables(q);bindings=action['case']['bindings']
        if len(free)!=1 or not free <= set(bindings):continue
        binding=next(iter(free));index=bindings.index(binding)
        if model['tables'][index]['datatype']!=rows:continue
        sort=result_sort(q)
        if sort not in ['U64','Bool']:continue
        empty=normal(sub(q,{binding:nil}),objects)
        if sort=='U64' and empty!={'U64':0}:continue
        if sort=='Bool' and empty not in [{'Bool':False},{'Bool':True}]:continue
        op='+' if sort=='U64' else '&&' if empty['Bool'] else '||'
        algebra=arithmetic if sort=='U64' else boolean.prove
        try:
            if sort=='U64':
                from producers.modular_aggregates import lift_sum
                modular=lift_sum(q,objects,add,word.compiler,word.cache/'modular')
                if modular:q=modular['term']
            contribution=fun([['summary_key',key_sort],['summary_value',row]],sort,sub(q,{binding:cons(rows,1,[k,v,nil])}))
            fold=fun([['summary_rows',R]],sort,match(xs,[([],empty),(['summary_key','summary_value','summary_tail'],binary(op,call(contribution,[k,v]),{'SelfCall':[tail]}))]),0)
            query=lambda r:sub(q,{binding:r});total=lambda r:call(fold,[r]);head=cons(rows,1,[k,v,tail]);a,z=query(xs),total(xs)
            tactic=Tactic(objects,algebra=algebra)
            proof={'Induction':dict(variable='summary_rows',**{'from':a,'to':z},cases=[dict(bindings=[],proof=tactic.prove(query(nil),total(nil))),dict(bindings=['summary_key','summary_value','summary_tail'],proof=tactic.prove(query(head),total(head),[(query(tail),total(tail),0)]))])}
            fusion=law([['summary_rows',R]],a,z,proof)
            raw_fold=fold
            if modular:
                project=lambda value:binary('&',value,{'U64':modular['mask']})
                observed_fold=fun([['summary_rows',R]],sort,project(call(fold,[xs])))
                fusion=law([['summary_rows',R]],sub(observed,{binding:xs}),call(observed_fold,[xs]),
                    trans(sub(modular['proof'],{binding:xs}),{'Substitute':dict(variable='modular_hole',context=project(var('modular_hole')),equality={'Use':dict(theorem=fusion,arguments=[xs],premises=[])})},convert(project(call(fold,[xs])),call(observed_fold,[xs]))))
                fold=observed_fold
            queries.append(dict(name=name,term=observed,binding=binding,index=index,sort=sort,empty=empty,op=op,contribution=contribution,fold=fold,raw_fold=raw_fold,fusion=fusion,observation_mask=modular['mask']if modular else None))
        except (ValueError,KeyError):
            # An inapplicable proposal grants no rewrite and leaves no unproved
            # declaration in the candidate closure.
            pass  # Only total definitions and independently valid algebra lemmas remain.
    summary=add({'Datatype':dict(constructors=[dict(name='QuerySummary',fields=[q['sort'] for q in queries])])});S={'Data':summary}
    build=lambda args:cons(summary,0,args);unit=build([q['empty'] for q in queries]);left=[f'summary_left_{i}' for i in range(len(queries))];right=[f'summary_right_{i}' for i in range(len(queries))]
    combine=fun([['summary_left',S],['summary_right',S]],S,match(var('summary_left'),[(left,match(var('summary_right'),[(right,build([binary(q['op'],var(a),var(b)) for q,a,b in zip(queries,left,right)]))]))]),0)
    merge=lambda a,z:call(combine,[a,z]);projections=[];rules=[]
    for i,q in enumerate(queries):
        ns=[f'summary_field_{i}_{j}' for j in range(len(queries))]
        field=fun([['summary',S]],q['sort'],match(var('summary'),[(ns,var(ns[i]))]),0);projections.append(field)
        a=call(field,[merge(var('summary_left'),var('summary_right'))]);z=binary(q['op'],call(field,[var('summary_left')]),call(field,[var('summary_right')]))
        lv,rv=build([var(n) for n in left]),build([var(n) for n in right]);p=convert(sub(a,{'summary_left':lv,'summary_right':rv}),sub(z,{'summary_left':lv,'summary_right':rv}))
        p={'Induction':dict(variable='summary_right',**{'from':sub(a,{'summary_left':lv}),'to':sub(z,{'summary_left':lv})},cases=[dict(bindings=right,proof=p)])}
        rules.append(law([['summary_left',S],['summary_right',S]],a,z,{'Induction':dict(variable='summary_left',**{'from':a,'to':z},cases=[dict(bindings=left,proof=p)])}))
    eta_args=[call(f,[var('summary')]) for f in projections];a,z=build(eta_args),var('summary');ns=[f'summary_eta_{i}' for i in range(len(queries))];bound=build([var(n) for n in ns])
    eta=law([['summary',S]],a,z,{'Induction':dict(variable='summary',**{'from':a,'to':z},cases=[dict(bindings=ns,proof=convert(sub(a,{'summary':bound}),bound))])})
    contribution=fun([['summary_key',key_sort],['summary_value',row]],S,build([call(q['contribution'],[k,v]) for q in queries]))
    fold=fun([['summary_rows',R]],S,match(xs,[([],unit),(['summary_key','summary_value','summary_tail'],merge(call(contribution,[k,v]),{'SelfCall':[tail]}))]),0)
    # Projections of the product fold are the independently admitted folds.
    for field,q in zip(projections,queries):
        a=call(field,[call(fold,[xs])]);z=call(q['raw_fold'],[xs]);head=cons(rows,1,[k,v,tail]);tactic=Tactic(objects,rules,opaque=[combine],algebra=arithmetic if q['sort']=='U64' else boolean.prove)
        p={'Induction':dict(variable='summary_rows',**{'from':a,'to':z},cases=[dict(bindings=[],proof=tactic.prove(sub(a,{'summary_rows':nil}),sub(z,{'summary_rows':nil}))),dict(bindings=['summary_key','summary_value','summary_tail'],proof=tactic.prove(sub(a,{'summary_rows':head}),sub(z,{'summary_rows':head}),[(call(field,[call(fold,[tail])]),call(q['raw_fold'],[tail]),0)]))])}
        raw_projection=law([['summary_rows',R]],a,z,p)
        if q['observation_mask']is not None:
            project=lambda value:binary('&',value,{'U64':q['observation_mask']})
            observed_field=fun([['summary',S]],q['sort'],project(call(field,[var('summary')])))
            left,right=call(observed_field,[call(fold,[xs])]),call(q['fold'],[xs])
            q['product_projection']=law([['summary_rows',R]],left,right,trans(convert(left,project(a)),{'Substitute':dict(variable='modular_hole',context=project(var('modular_hole')),equality={'Use':dict(theorem=raw_projection,arguments=[xs],premises=[])})},convert(project(z),right)))
            q['projection']=observed_field
        else:q['product_projection']=raw_projection;q['projection']=field
    def product_arithmetic(a,z):
        parts=[]
        for field,q in zip(projections,queries):
            tactic=Tactic(objects,rules,opaque=[combine],algebra=arithmetic if q['sort']=='U64' else boolean.prove)
            parts.append(tactic.prove(call(field,[a]),call(field,[z])))
        use=lambda t:{'Use':dict(theorem=eta,arguments=[t],premises=[])}
        return trans({'Sym':use(a)},{'Construct':dict(datatype=summary,constructor=0,arguments=parts)},use(z))
    # The second historical slot is a zero word. Its layout and proof roles stay
    # compatible; the first slot now contains any finite typed product.
    zero_contribution=fun([['summary_value',row]],'U64',{'U64':0})
    zero_fold=fun([['summary_rows',R]],'U64',match(xs,[([],{'U64':0}),(['summary_key','summary_value','summary_tail'],binary('+',{'U64':0},{'SelfCall':[tail]}))]),0)
    zero_fusion=law([['summary_rows',R]],call(zero_fold,[xs]),call(zero_fold,[xs]),{'Refl':call(zero_fold,[xs])})
    product_fusion=law([['summary_rows',R]],call(fold,[xs]),call(fold,[xs]),{'Refl':call(fold,[xs])})
    return [dict(sort=S,empty=unit,contribution=contribution,contribution_keys=True,fold=fold,fusion=product_fusion,updates={},combine=merge,opaque=[combine],prove_arithmetic=product_arithmetic,queries=queries),dict(sort='U64',contribution=zero_contribution,fold=zero_fold,fusion=zero_fusion,updates={},combine=lambda a,z:binary('+',a,z),prove_arithmetic=arithmetic)]
