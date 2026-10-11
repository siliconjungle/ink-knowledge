"""Lift point maintenance through total, presence-preserving Option mappers.

Ordinary equality congruence, Boolean cases and Option induction establish every
law. Record field dependencies are terms, never trusted invalidation metadata.
"""
import copy
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import binary,choice,match,sub,lift,equality,free_variables,normal,replace


def setup(model,cache,add,objects,dynamic):
    reply=cache['case']['normal']['Construct']['arguments'][0]
    mapped=reply['Match'];source=mapped['scrutinee'];branches=mapped['branches']
    if 'Call'not in source or len(branches)!=2 or branches[0]['bindings'] or len(branches[1]['bindings'])!=1:
        raise ValueError('unsupported point mapper branches')
    no,yes=(b['body'].get('Construct',{})for b in branches)
    if no.get('constructor')!=0 or no.get('arguments') or yes.get('constructor')!=1 or len(yes.get('arguments',[]))!=1 or no.get('datatype')!=yes.get('datatype'):
        raise ValueError('point mapper must preserve Option presence')
    binder=branches[1]['bindings'][0];body=yes['arguments'][0]
    if free_variables(body)-{binder}:raise ValueError('point mapper captures additional state')
    fake=copy.deepcopy(cache);fake['case']['normal']['Construct']['arguments'][0]=source
    if dynamic:
        from producers.point_delta_dynamic import setup as raw_setup
    else:
        from producers.point_delta import setup as raw_setup
    raw=raw_setup(model,fake,add,objects);table=raw['table'];d=table['datatype'];q=raw['q'];index=raw['index']
    raw_option=objects[raw['get']]['payload']['declaration']['Function']['result'];row_sort=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    option=yes['datatype'];output={'Data':option};none=cons(option,0,[])
    project=lambda x:sub(body,{binder:x})
    some=lambda x:cons(option,1,[project(x)])
    carriers=[key for key,value in objects.items()if 'Datatype'in value['payload'].get('declaration',{})]
    function=lambda ps,result,body:add({'Function':dict(params=ps,result=result,body=body,recursive=None)},carriers)
    mapper=function([['mapped_input',raw_option]],output,
                    match(var('mapped_input'),[(b['bindings'],b['body'])for b in branches]))
    mapped_value=lambda x:call(mapper,[x])
    get=function([['mapped_rows',{'Data':d}],['mapped_key','U64']],output,
                 mapped_value(call(raw['get'],[var('mapped_rows'),var('mapped_key')])))
    getof=lambda rows:call(get,[rows,q])
    raw_get=lambda rows:call(raw['get'],[rows,q])
    theorem=lambda ps,a,z,proof:add({'Theorem':dict(params=ps,conditions=[],**{'from':a,'to':z},proof=proof)},carriers)
    use=lambda law,args:{'Use':dict(theorem=law,arguments=args,premises=[])}

    # Map commutes with a conditional; map of an optional replacement keeps
    # exactly the same absence/presence distinction as the original read.
    cond,left,right=map(var,['mapped_condition','mapped_left','mapped_right'])
    a=mapped_value(choice(cond,left,right));z=choice(cond,mapped_value(left),mapped_value(right))
    if_law=theorem([['mapped_condition','Bool'],['mapped_left',raw_option],['mapped_right',raw_option]],a,z,
                   {'BoolSplit':dict(condition=cond,**{'from':a,'to':z},
                                     on_true=equality(a,z,objects,facts=[(cond,{'Bool':True},0)]),
                                     on_false=equality(a,z,objects,facts=[(cond,{'Bool':False},0)]))})
    before,new=var('mapped_before'),var('mapped_new')
    raw_none=cons(raw_option['Data'],0,[]);raw_some=lambda x:cons(raw_option['Data'],1,[x])
    replaced=lambda x:match(x,[([],raw_none),(['mapped_previous'],raw_some(new))])
    predicted=lambda x:match(mapped_value(x),[([],none),(['mapped_previous'],some(new))])
    a=mapped_value(replaced(before));z=predicted(before)
    replace_law=theorem([['mapped_before',raw_option],['mapped_new',row_sort]],a,z,
                        {'Induction':dict(variable='mapped_before',**{'from':a,'to':z},cases=[
                            dict(bindings=[],proof=convert(mapped_value(replaced(raw_none)),predicted(raw_none))),
                            dict(bindings=['mapped_original'],proof=convert(mapped_value(replaced(raw_some(var('mapped_original')))),predicted(raw_some(var('mapped_original'))))),
                        ])})
    laws={}
    for name,raw_law in (raw.get('laws')or raw['updates']).items():
        decl=objects[raw_law]['payload']['declaration']['Theorem'];ps=decl['params'];args=[var(n)for n,_ in ps]
        rows=args[0];target=args[1]if dynamic else q;new=args[-1]if name!='remove'else None
        changed=call(table[name],[rows,target]+([new]if new is not None else[]))
        same=none if name=='remove'else match(getof(rows),[([],none),(['mapped_old'],some(new))])if name=='replace'else getof(changed)
        desired=choice(binary('==',target,q),same,getof(rows))if dynamic else same
        proof=trans(convert(getof(changed),mapped_value(decl['from'])),lift(use(raw_law,args),mapped_value(var('delta_hole'))))
        if dynamic:
            raw_if=decl['to']['If'];guard=raw_if['condition']
            proof=trans(proof,use(if_law,[guard,raw_if['on_true'],raw_if['on_false']]))
            if name=='replace':
                context=choice(guard,var('delta_hole'),mapped_value(raw_get(rows)))
                proof=trans(proof,lift(use(replace_law,[raw_get(rows),new]),context))
        elif name=='replace':proof=trans(proof,use(replace_law,[raw_get(rows),new]))
        # Alpha conversion and literal unfolding are checked independently.
        current=(choice(binary('==',target,q),predicted(raw_get(rows))if name=='replace'else mapped_value(decl['to']['If']['on_true']),mapped_value(raw_get(rows)))if dynamic
                 else predicted(raw_get(rows))if name=='replace'else mapped_value(decl['to']))
        laws[name]=theorem(ps,getof(changed),desired,trans(proof,convert(current,desired)))

    def alpha(t, env=None, depth=0):
        env=env or {}
        if isinstance(t, list): return [alpha(x,env,depth)for x in t]
        if not isinstance(t, dict): return t
        if set(t)=={'Var'}: return var(env.get(t['Var'],t['Var']))
        if 'Match' in t:
            x=t['Match']; branches=[]
            for b in x['branches']:
                ns=['field_bound_'+str(depth)+'_'+str(i)for i in range(len(b['bindings']))]
                branches.append((ns,alpha(b['body'],{**env,**dict(zip(b['bindings'],ns))},depth+1)))
            return match(alpha(x['scrutinee'],env,depth),branches)
        return {k:alpha(v,env,depth)for k,v in t.items()}

    def alpha_replace(t,a,z):
        if isinstance(t,dict) and alpha(t)==alpha(a): return z
        if isinstance(t,dict):return {k:alpha_replace(v,a,z)for k,v in t.items()}
        if isinstance(t,list):return [alpha_replace(v,a,z)for v in t]
        return t

    preserved = {}
    action_params = {}
    def preservation(root, new):
        # Prove that a replacement preserves this mapper over every optional
        # old row. Looking only at field names would be insufficient.
        if dynamic: return None
        before = var('field_before')
        raw_read = raw_get(root)
        expression = replace(project(new), raw_read, before)
        free = free_variables(expression) - {'field_before'}
        if not free <= set(action_params): return None
        cache_key = str((expression, sorted(free)))
        if cache_key in preserved:
            saved=preserved[cache_key]
            if not saved:return None
            law,_,left,right=saved
            return law,[raw_get(root),*[var(n)for n in sorted(free)]],left,right
        left = match(mapped_value(before), [([],none),(['field_cached'],cons(option,1,[expression]))])
        right = mapped_value(before)
        cases=[]
        for value,names in [(raw_none,[]),(raw_some(var('field_original')),['field_original'])]:
            a,z=sub(left,{'field_before':value}),sub(right,{'field_before':value})
            if alpha(normal(a,objects))!=alpha(normal(z,objects)):
                preserved[cache_key]=None;return None
            cases.append(dict(bindings=names,proof=convert(a,z)))
        params=[['field_before',raw_option],*[[n,action_params[n]]for n in sorted(free)]]
        law=theorem(params,left,right,{'Induction':dict(variable='field_before',**{'from':left,'to':right},cases=cases)})
        result=(law,[raw_get(root),*[var(n)for n in sorted(free)]],left,right)
        preserved[cache_key]=result
        return result

    def recipe(t,old,bindings):
        if t==var(bindings[index]):return old
        x=t.get('Call',{});args=x.get('arguments',[])
        name=next((n for n in laws if table[n]==x.get('function')),None)
        if name is None or len(args)<2 or (not dynamic and args[1]!=q):raise ValueError('unsupported mapped point update')
        prior=recipe(args[0],old,bindings)
        if name=='replace' and preservation(args[0],args[2]): return prior
        same=none if name=='remove'else match(prior,[([],none),(['mapped_old'],some(args[2]))])if name=='replace'else getof(t)
        return choice(binary('==',args[1],q),same,prior)if dynamic else same

    def action(source_action):
        action_params.update(dict(source_action['params']))
        def predict(t):
            if 'If'in t:
                x=t['If'];a,z=predict(x['on_true']),predict(x['on_false'])
                return a if alpha(a)==alpha(z) else choice(x['condition'],a,z)
            x=t['Construct']
            if x['constructor']!=0 or x['arguments'][1]!={'Bool':True}:return var('cached_reply')
            return recipe(x['arguments'][3]['Construct']['arguments'][index],var('cached_reply'),source_action['case']['bindings'])
        try:return predict(source_action['case']['normal'])
        except(ValueError,KeyError):return None

    def query_equality(t,bindings):
        if t==var(bindings[index]):return {'Refl':getof(t)}
        x=t['Call'];args=x['arguments'];name=next(n for n in laws if table[n]==x['function'])
        proof=use(laws[name],args if dynamic else [args[0]]+([args[2]]if name=='replace'else[]))
        preserving=preservation(args[0],args[2]) if name=='replace' else None
        if preserving:
            law,arguments,_,_=preserving
            current=match(getof(args[0]),[([],none),(['mapped_old'],some(args[2]))])
            return trans(proof,convert(current,sub(objects[law]['payload']['declaration']['Theorem']['from'],dict(zip([n for n,_ in objects[law]['payload']['declaration']['Theorem']['params']],arguments)))),use(law,arguments),convert(mapped_value(raw_get(args[0])),getof(args[0])),query_equality(args[0],bindings))
        prior=getof(args[0]);same=none if name=='remove'else match(prior,[([],none),(['mapped_old'],some(args[2]))])if name=='replace'else getof(t)
        context=choice(binary('==',args[1],q),same,prior)if dynamic else same
        from producers.point_delta import replace
        return trans(proof,lift(query_equality(args[0],bindings),replace(context,prior,var('delta_hole'))))

    return dict(action=action,recipe=recipe,equality=query_equality,index=index,get=get,q=q,option=option,table=table,some=some,
                start=lambda a,z,facts:equality(a,z,objects,facts=facts,rewrite=alpha_replace if any(preserved.values()) else replace))
