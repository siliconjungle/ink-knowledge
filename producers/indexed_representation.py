"""Source-bound whole-action admission for indexed cached table definitions.

External authoring only. No selector or runtime source evaluator is introduced.
"""
from action_replacement import var,call,cons,convert,trans
from point_delta import sub,choice
from representations import match,refs
from state_laws import derive
from ink_knowledge import identity
from ink_knowledge.store import entry

def proposal(model,objects,names,add,fun,law):
    tree=names['tree'];T={'Data':tree};L={'Data':model['state']};rows=model['tables'][0]['datatype'];table=model['tables'][0]
    Pid=add({'Datatype':{'constructors':[{'name':'IndexedTableState','fields':[T]}]}},name='physical_state');P={'Data':Pid};physical=lambda t:cons(Pid,0,[t]);logical=lambda t:cons(model['state'],0,[call(names['decode'],[t])]);fix=lambda t:call(names['repair'],[t]);decode_rows=lambda t:call(names['decode'],[t])
    def use(i,args,premises=()):return {'Use':dict(theorem=i,arguments=args,premises=list(premises))}
    def lift(p,context):return {'Substitute':dict(variable='indexed_hole',context=context,equality=p)}
    hole=var('indexed_hole')
    encode=fun('encode',[['logical',L]],P,match(var('logical'),[(['initial_rows'],physical(call(names['encode_rows'],[var('initial_rows')])))]))
    decode=fun('decode_state',[['physical',P]],L,match(var('physical'),[(['physical_tree'],logical(var('physical_tree')))]))
    view=fun('tree_of',[['physical',P]],T,match(var('physical'),[(['physical_tree'],var('physical_tree'))]))
    repair_p=fun('repair_state',[['physical',P]],P,physical(fix(call(view,[var('physical')]))))
    eta=law(None,[['physical',P]],physical(call(view,[var('physical')])),var('physical'),{'Induction':dict(variable='physical',**{'from':physical(call(view,[var('physical')])),'to':var('physical')},cases=[dict(bindings=['eta_tree'],proof=convert(physical(call(view,[physical(var('eta_tree'))])),physical(var('eta_tree'))))])})
    decode_eta=law(None,[['physical',P]],call(decode,[var('physical')]),logical(call(view,[var('physical')])),{'Induction':dict(variable='physical',**{'from':call(decode,[var('physical')]),'to':logical(call(view,[var('physical')]))},cases=[dict(bindings=['eta_tree'],proof=convert(call(decode,[physical(var('eta_tree'))]),logical(var('eta_tree'))))])})
    rel0_l=fun('logical_relation_left',[['physical',P],['logical',L]],L,call(decode,[var('physical')]))
    rel0_r=fun('logical_relation_right',[['physical',P],['logical',L]],L,var('logical'))
    rel1_l=fun('metadata_relation_left',[['physical',P],['logical',L]],T,fix(call(view,[var('physical')])))
    rel1_r=fun('metadata_relation_right',[['physical',P],['logical',L]],T,call(view,[var('physical')]))
    relations=[dict(left=rel0_l,right=rel0_r),dict(left=rel1_l,right=rel1_r)]
    x=var('initial_rows');bound=cons(model['state'],0,[x]);encoded=physical(call(names['encode_rows'],[x]));initial=[]
    for a,z,p in [(call(decode,[call(encode,[var('logical')])]),var('logical'),{'Construct':dict(datatype=model['state'],constructor=0,arguments=[use(names['encode_preserves_rows'],[x])])}),(fix(call(view,[call(encode,[var('logical')])])),call(view,[call(encode,[var('logical')])]),use(names['encode_preserves_metadata'],[x]))]:
        # Explicit conversion connects the fixed source state projection with
        # the universally proved row encoding fact.
        aa,zz=sub(a,{'logical':bound}),sub(z,{'logical':bound})
        middle_a=logical(call(names['encode_rows'],[x])) if len(initial)==0 else fix(call(names['encode_rows'],[x]));middle_z=bound if len(initial)==0 else call(names['encode_rows'],[x])
        initial.append({'Induction':dict(variable='logical',**{'from':a,'to':z},cases=[dict(bindings=['initial_rows'],proof=trans(convert(aa,middle_a),p,convert(middle_z,zz)))])})
    raw=var('indexed_tree');root=fix(raw);source_rows=decode_rows(raw);binding=model['actions']['put']['case']['bindings'][0]
    rules=[(decode_rows(root),source_rows,use(names['repair_preserves_rows'],[raw]))]
    metadata_rules=[(fix(root),root,use(names['repair_idempotent'],[raw]))]
    query_terms=[(model['actions'][action]['case']['normal']['Construct']['arguments'][0],label) for action,label in [('total_query','sum'),('count_query','count')]]
    def mapped(t):
        if t==var(binding):return var('physical_tree')
        for term,label in query_terms:
            if t==term:
                p=trans(use(names[label+'_repair_matches_rows'],[raw]),{'Sym':use(names[label+'_fusion'],[source_rows])})
                rules.append((call(names[label],[root]),sub(term,{binding:source_rows}),p));return call(names[label],[var('physical_tree')])
        if isinstance(t,list):return [mapped(v) for v in t]
        if not isinstance(t,dict):return t
        if 'Call'in t and t['Call']['function'] in [table[k] for k in ['get','insert','replace','remove']]:
            c=t['Call'];operation=next(k for k in ['get','insert','replace','remove'] if c['function']==table[k]);args=[mapped(v) for v in c['arguments']];f=names['lookup' if operation=='get' else operation];result=call(f,args)
            # This producer admits the single-table, single-update action domain.
            if c['arguments'][0]!=var(binding):raise ValueError('nested table mutation needs a composed checked lemma')
            actual=sub(result,{'physical_tree':root});logical_args=[sub(v,{binding:source_rows}) for v in c['arguments']]
            if operation=='get':
                p=trans(use(names['indexed_lookup_preserves_rows'],[raw,*args[1:]]),use(names['lookup_preserves_rows'],[raw,*args[1:]]));rules.append((actual,call(c['function'],logical_args),p))
            else:
                p=use(names['indexed_'+operation+'_preserves_rows'],[raw,*args[1:]]);rules.append((decode_rows(actual),call(c['function'],logical_args),p))
                metadata_rules.append((fix(actual),actual,use(names['indexed_'+operation+'_preserves_metadata'],[raw,*args[1:]])))
            return result
        if 'Construct'in t and t['Construct']['datatype']==model['state']:return physical(mapped(t['Construct']['arguments'][0]))
        return {k:mapped(v) for k,v in t.items()}
    actions={}
    for action,a in model['actions'].items():
        result_id=a['result']['Data'];constructors=objects[result_id]['payload']['declaration']['Datatype']['constructors'];cs=[]
        for c in constructors:cs.append(dict(name=c['name'],fields=[P if ty==L else ty for ty in c['fields']]))
        carrier=add({'Datatype':dict(constructors=cs)},name='transition_'+action);X={'Data':carrier}
        body=mapped(a['case']['normal'])
        def outcomes(t):
            if isinstance(t,list):return [outcomes(v) for v in t]
            if not isinstance(t,dict):return t
            if 'Construct'in t and t['Construct']['datatype']==result_id:return {'Construct':{**t['Construct'],'datatype':carrier,'arguments':outcomes(t['Construct']['arguments'])}}
            return {k:outcomes(v) for k,v in t.items()}
        body=outcomes(body);rest=a['params'][1:];args=[var(n) for n,_ in rest]
        execute=fun('execute_'+action,[['initial',P],*rest],X,match(var('initial'),[(['physical_tree'],body)]))
        normal_names=['observed_reply','observed_committed','observed_version','observed_state','observed_events'];host_names=['observed_host','observed_version','observed_state'];branches=[normal_names,host_names]
        observe=fun('observe_'+action,[['transition',X]],a['result'],match(var('transition'),[(ns,cons(result_id,j,[call(decode,[var(n)]) if n=='observed_state' else var(n) for n in ns])) for j,ns in enumerate(branches)]))
        nextf=fun('next_'+action,[['transition',X]],P,match(var('transition'),[(ns,var('observed_state')) for ns in branches]))
        executed=call(execute,[physical(root),*args]);observed=call(observe,[executed]);source=call(a['function'],[logical(raw),*args])
        observation=law(None,[['indexed_tree',T],*rest],observed,source,derive(observed,source,objects,rules=rules))
        newtree=call(view,[call(nextf,[executed])]);metadata=law(None,[['indexed_tree',T],*rest],fix(newtree),newtree,derive(fix(newtree),newtree,objects,rules=metadata_rules))
        # Every carrier constructor has the same decode/next commuting equation.
        def post(t):return match(t,[(normal_names,var('observed_state')),(host_names,var('observed_state'))])
        t=var('transition');left=call(decode,[call(nextf,[t])]);right=post(call(observe,[t]));carrier_cases=[]
        for j,ns in enumerate(branches):
            v=cons(carrier,j,[var(n) for n in ns]);carrier_cases.append(dict(bindings=ns,proof=convert(sub(left,{'transition':v}),sub(right,{'transition':v}))))
        commuting=law(None,[['transition',X]],left,right,{'Induction':dict(variable='transition',**{'from':left,'to':right},cases=carrier_cases)})
        p,l=var('physical'),var('logical');repair_equal=trans(convert(call(repair_p,[p]),physical(fix(call(view,[p])))),{'Construct':dict(datatype=Pid,constructor=0,arguments=[{'Hypothesis':1}])},use(eta,[p]))
        run=lambda p:call(execute,[p,*args]);obs=lambda p:call(observe,[run(p)]);nexttree=lambda p:call(view,[call(nextf,[run(p)])]);source_l=call(a['function'],[l,*args])
        observe_eq=trans(lift({'Sym':repair_equal},obs(hole)),convert(obs(call(repair_p,[p])),call(observe,[call(execute,[physical(fix(call(view,[p]))),*args])])),use(observation,[call(view,[p]),*args]),lift({'Sym':use(decode_eta,[p])},call(a['function'],[hole,*args])),lift({'Hypothesis':0},call(a['function'],[hole,*args])))
        preserve_rows=trans(use(commuting,[run(p)]),lift(observe_eq,post(hole)))
        preserve_metadata=trans(lift({'Sym':repair_equal},fix(nexttree(hole))),convert(fix(nexttree(call(repair_p,[p]))),sub(fix(newtree),{'indexed_tree':call(view,[p])})),use(metadata,[call(view,[p]),*args]),convert(sub(newtree,{'indexed_tree':call(view,[p])}),nexttree(call(repair_p,[p]))),lift(repair_equal,nexttree(hole)))
        actions[action]=dict(execute=execute,result=X,next=nextf,observe=observe,preservation=[preserve_rows,preserve_metadata],observation=observe_eq)
    plan=dict(source_objects=sorted(model['objects']),logical_state=L,physical_state=P,encode=encode,decode=decode,relations=relations,initialisation=initial,snapshot={'Hypothesis':0},actions=actions)
    obj=entry('representation','ink-source-representation-v1',plan,refs(plan),parameters={'logical':L},result=P,effects=['source-transitions']);obj['interface']['operations']=sorted(actions);i=identity(obj);objects[i]=obj;names['representation']=i
    return i
