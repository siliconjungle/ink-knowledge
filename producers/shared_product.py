"""Share one proved observation across independently supplied cache maintainers.

No cache metadata establishes correctness. Projection/eta induction and the
components' complete observation proofs justify reuse for every future action.
"""
from action_replacement import var, call, cons, convert, trans
from representations import match
from point_delta import sub, replace


def share(model, plans, actions, physical, getters, relations, offsets, objects, function, theorem, observers):
    def use(key, args, premises=()):
        return {'Use': dict(theorem=key, arguments=args, premises=list(premises))}
    def lift(proof, context):
        return {'Substitute': dict(variable='shared_hole', context=context, equality=proof)}
    def projected(term, index, result_id):
        if 'Construct' in term and term['Construct']['datatype'] == result_id:
            return term['Construct']['arguments'][index]
        if 'If' in term:
            x = term['If']; return {'If': dict(condition=x['condition'], on_true=projected(x['on_true'],index,result_id), on_false=projected(x['on_false'],index,result_id))}
        if 'Match' in term:
            x = term['Match']; return match(x['scrutinee'], [(b['bindings'],projected(b['body'],index,result_id))for b in x['branches']])
        raise ValueError('shared maintenance needs a structurally exposed result carrier')
    def bind_law(params, body, left, right, variable, constructors):
        cases=[]
        for tag,c in enumerate(constructors):
            ns=['shared_case_'+str(tag)+'_'+str(i)for i in range(len(c['fields']))]
            value=cons(dict(params)[variable]['Data'],tag,[var(n)for n in ns])
            cases.append(dict(bindings=ns,proof=convert(sub(left,{variable:value}),sub(right,{variable:value}))))
        return theorem(params,[],left,right,{'Induction':dict(variable=variable,**{'from':left,'to':right},cases=cases)})
    logical={'Data':model['state']}
    conditions=[]
    for relation in relations:
        conditions.append({'from':call(relation['left'],[var('physical'),var('logical')]),
                           'to':call(relation['right'],[var('physical'),var('logical')])})
    for name, source in model['actions'].items():
        action=actions[name]; rest=source['params'][1:]; args=[var(n)for n,_ in rest]
        params=[['physical',physical],['logical',logical],*rest]
        chosen=observers.get(name,0)
        selected=lambda i:call(getters[i],[var('physical')])
        old_executed=call(action['execute'],[var('physical'),*args])
        original=call(source['function'],[var('logical'),*args])
        components=[];common_proof=None
        for i,plan in enumerate(plans):
            a=plan['actions'][name];rid=a['result']['Data']
            constructors=objects[rid]['payload']['declaration']['Datatype']['constructors']
            if len(constructors)!=1 or len(constructors[0]['fields'])!=2 or constructors[0]['fields'][1]!=source['result']:
                raise ValueError('shared maintenance needs cache carriers with an independent observation')
            fields=constructors[0]['fields']; ns=['shared_retained','shared_observed']
            # Checkable eta, not a trusted promise that the envelope has no other meaning.
            get_retained=function([['executed',a['result']]],fields[0],match(var('executed'),[(ns,var(ns[0]))]),recursive=0)
            get_observed=function([['executed',a['result']]],source['result'],match(var('executed'),[(ns,var(ns[1]))]),recursive=0)
            eta_a=cons(rid,0,[call(get_retained,[var('executed')]),call(get_observed,[var('executed')])])
            eta=bind_law([['executed',a['result']]],None,eta_a,var('executed'),'executed',constructors)
            initial=objects[plan['physical_state']['Data']]['payload']['declaration']['Datatype']['constructors']
            execute=objects[a['execute']]['payload']['declaration']['Function']
            branches=[]
            from point_delta import normal
            for tag,c in enumerate(initial):
                bindings=['shared_input_'+str(tag)+'_'+str(j)for j in range(len(c['fields']))]
                bound=cons(plan['physical_state']['Data'],tag,[var(n)for n in bindings])
                reduced=normal(call(a['execute'],[bound,*args]),objects)
                branches.append((bindings,projected(reduced,0,rid)))
            retain=function([['physical',plan['physical_state']],*rest],fields[0],match(var('physical'),branches),recursive=0)
            # A native implementation must not execute the observation just to
            # recover the retained fields. Recheck the direct projection equation.
            retained_a=call(retain,[var('physical'),*args]); retained_z=call(get_retained,[call(a['execute'],[var('physical'),*args])])
            retained_law=bind_law([['physical',plan['physical_state']],*rest],None,retained_a,retained_z,'physical',initial)
            base_conditions=[{'from':call(r['left'],[var('physical'),var('logical')]),'to':call(r['right'],[var('physical'),var('logical')])}for r in plan['relations']]
            observed=call(a['observe'],[call(a['execute'],[var('physical'),*args])])
            observation_law=theorem([['physical',plan['physical_state']],['logical',logical],*rest],base_conditions,observed,original,a['observation'])
            proof=use(observation_law,[selected(i),var('logical'),*args],[{'Hypothesis':offsets[i]+j}for j in range(len(plan['relations']))])
            observe_eta=bind_law([['executed',a['result']]],None,call(a['observe'],[var('executed')]),call(get_observed,[var('executed')]),'executed',constructors)
            components.append(dict(a=a,rid=rid,retain=retain,retained_law=retained_law,observed=observed,proof=proof,eta=eta,observe_eta=observe_eta,get_retained=get_retained,get_observed=get_observed))
        selected_action=plans[chosen]['actions'][name]
        common=call(selected_action['observe'],[call(selected_action['execute'],[selected(chosen),*args])])
        common_proof=components[chosen]['proof']
        result_id=action['result']['Data']
        observation_id=source['result']['Data']
        observation_constructors=objects[observation_id]['payload']['declaration']['Datatype']['constructors']
        # A single match binds the observation once before constructing all cache
        # carriers. The retain functions contain only their required inputs.
        def assembled(observation):
            return cons(result_id,0,[cons(c['rid'],0,[call(c['retain'],[selected(i),*args]),observation])for i,c in enumerate(components)])
        branches=[]
        for tag,c in enumerate(observation_constructors):
            ns=['shared_obs_'+str(tag)+'_'+str(i)for i in range(len(c['fields']))]
            branches.append((ns,assembled(cons(observation_id,tag,[var(n)for n in ns]))))
        binder=function([['physical',physical],*rest,['common',source['result']]],action['result'],match(var('common'),branches),recursive=len(rest)+1)
        bind_left=call(binder,[var('physical'),*args,var('common')]);bind_right=assembled(var('common'))
        bind_eta=bind_law([['physical',physical],*rest,['common',source['result']]],None,bind_left,bind_right,'common',observation_constructors)
        shared_execute=function([['physical',physical],*rest],action['result'],call(binder,[var('physical'),*args,common]))
        shared=call(shared_execute,[var('physical'),*args])
        assembled_common=assembled(common)
        steps=[convert(shared,call(binder,[var('physical'),*args,common])),use(bind_eta,[var('physical'),*args,common])]
        element_proofs=[]
        for i,c in enumerate(components):
            executed=call(c['a']['execute'],[selected(i),*args])
            common_to_other=trans(common_proof,{'Sym':c['proof']},
                use(c['observe_eta'],[executed]))
            first=use(c['retained_law'],[selected(i),*args])
            element_proofs.append(trans({'Construct':dict(datatype=c['rid'],constructor=0,arguments=[first,common_to_other])},use(c['eta'],[executed])))
        steps.append({'Construct':dict(datatype=result_id,constructor=0,arguments=element_proofs)})
        steps.append(convert(cons(result_id,0,[call(c['a']['execute'],[selected(i),*args])for i,c in enumerate(components)]),old_executed))
        equality=theorem(params,conditions,shared,old_executed,trans(*steps))
        proof=use(equality,[var('physical'),var('logical'),*args],[{'Hypothesis':i}for i in range(len(conditions))])
        old_observed=call(action['observe'],[old_executed])
        base_observation=theorem(params,conditions,old_observed,original,action['observation'])
        action['observation']=trans(lift(proof,call(action['observe'],[var('shared_hole')])),use(base_observation,[var('physical'),var('logical'),*args],[{'Hypothesis':i}for i in range(len(conditions))]))
        post=match(original,[(['r','c','v','s','e'],var('s')),(['h','v','s'],var('s'))])
        base_preservation=[theorem(params,conditions,call(r['left'],[call(action['next'],[old_executed]),post]),call(r['right'],[call(action['next'],[old_executed]),post]),p)for r,p in zip(relations,action['preservation'])]
        action['preservation']=[trans(lift(proof,call(r['left'],[call(action['next'],[var('shared_hole')]),post])),use(p,[var('physical'),var('logical'),*args],[{'Hypothesis':i}for i in range(len(conditions))]),
            {'Sym':lift(proof,call(r['right'],[call(action['next'],[var('shared_hole')]),post]))})for r,p in zip(relations,base_preservation)]
        action['execute']=shared_execute
