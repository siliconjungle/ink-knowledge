"""Database-owned, universally checked equality-guarded word replacement.

This recipe only proposes implementations. The normal maintained-fold admission
replays both the previous update equation and the complete 64-bit RUP proof.
No source names, profiles, bounded samples or trusted arithmetic matcher grant
permission to skip work.
"""
import copy, gzip, json
from pathlib import Path
from ink_knowledge import Store, identity
from ink_knowledge.store import entry
from producers.action_replacement import var, call, convert, trans
from producers.point_delta import binary, normal
from producers.representations import refs


def guarded_word_update(package, directory, zero=False):
    package=copy.deepcopy(package)
    objects=package['knowledge']['objects']
    proof_name='word-update-guarded-zero.json.gz' if zero else 'word-update-equal.json.gz'
    proof=json.loads(gzip.decompress((Path(__file__).parent/'data'/proof_name).read_bytes()))
    original=proof['BitVector']['from'];guarded=proof['BitVector']['to']
    params=[['total','U64'],['old','U64'],['new','U64']]
    def add(kind,declaration):
        payload=dict(declaration=declaration);body=next(iter(declaration.values()))
        obj=entry(kind,'first-order-inductive-equality-v1',payload,refs(payload),parameters=dict(body['params']),result=body.get('result'),conditions=body.get('conditions',[]))
        key=identity(obj);objects[key]=obj;return key
    theorem=None;function=None;changed=0
    for view in package['views']:
        previous=view.get('update')
        if not previous:continue
        old=call(previous['function'],[var(n) for n,_ in params])
        # This is an untrusted applicability hint, followed by Convert admission.
        if normal(old,objects)!=original:continue
        if theorem is None:
            theorem=add('theorem',{'Theorem':dict(params=params,conditions=[],**{'from':original,'to':guarded},proof=proof)})
            function=add('definition',{'Function':dict(params=params,result='U64',body=guarded,recursive=None)})
        new=call(function,[var(n) for n,_ in params])
        view['update']=dict(function=function,proof=trans(previous['proof'],convert(old,original),{'Use':dict(theorem=theorem,arguments=[var(n) for n,_ in params],premises=[])},convert(guarded,new)))
        changed+=1
    if not changed:raise ValueError('no checked word replacement proposal applies')
    store=Store.publish(Path(directory),list(objects.values()))
    package['knowledge']=store.bundle(sorted(objects))
    return package


def predicate_row_update(package, directory):
    """Propose predicate transitions without materialising absent contributions.

    Detection is only an authoring hint. The generic row-update gate checks the
    complete equation, including contribution-choice and word-group laws.
    Fixed weights get a predicate-equality guard. Row-dependent weights get
    direct Boolean branches and an equality guard only when both contribute.
    """
    from producers.point_delta import choice, sub, free_variables
    package=copy.deepcopy(package);objects=package['knowledge']['objects']
    def add(kind,declaration):
        payload=dict(declaration=declaration);body=next(iter(declaration.values()))
        obj=entry(kind,'first-order-inductive-equality-v1',payload,refs(payload),parameters=dict(body['params']),result=body.get('result'),conditions=body.get('conditions',[]))
        key=identity(obj);objects[key]=obj;return key
    theorems={};changed=0
    for view in package['views']:
        original=view['contribution'];selected=view.get('contribution_choice',{}).get('function',original)
        f=objects[original]['payload']['declaration']['Function'];key_sort,row_sort=[s for _,s in f['params']]
        c=normal(call(selected,[var('key'),var('row')]),objects)
        if 'If' not in c:continue
        c=c['If'];weight=c['on_true']
        if c['on_false']!={'U64':0} or free_variables(weight)-{'key','row'}:continue
        fixed=not (free_variables(weight)-{'key'})
        name='word-boolean-transition.json.gz' if fixed else 'word-predicate-transition.json.gz'
        proof=json.loads(gzip.decompress((Path(__file__).parent/'data'/name).read_bytes()))
        equation=proof['BitVector'] if fixed else proof['WordExtensionality']
        before=sub(c['condition'],{'row':var('old')});after=sub(c['condition'],{'row':var('new')})
        args=[var('total'),weight,before,after] if fixed else [var('total'),sub(weight,{'row':var('old')}),sub(weight,{'row':var('new')}),before,after]
        theorem_params=[['total','U64'],['weight','U64'],['old','Bool'],['new','Bool']] if fixed else [['total','U64'],['before','U64'],['after','U64'],['old','Bool'],['new','Bool']]
        mapping=dict(zip([n for n,_ in theorem_params],args));a=sub(equation['from'],mapping);z=sub(equation['to'],mapping)
        contrib=lambda fn,row:call(fn,[var('key'),var(row)])
        combine=lambda a,b:call(view['combine'],[a,b])
        inverse=lambda a:call(view['inverse'],[a])
        left=combine(combine(var('total'),inverse(contrib(original,'old'))),contrib(original,'new'))
        selected_left=combine(combine(var('total'),inverse(contrib(selected,'old'))),contrib(selected,'new'))
        # Refuse groups whose normalised operations do not match this word law.
        if normal(selected_left,objects)!=a:continue
        if name not in theorems:
            theorems[name]=add('theorem',{'Theorem':dict(params=theorem_params,conditions=[],**{'from':equation['from'],'to':equation['to']},proof=proof)})
        theorem=theorems[name]
        params=[['total','U64'],['key',key_sort],['old',row_sort],['new',row_sort]]
        function=add('definition',{'Function':dict(params=params,result='U64',body=z,recursive=None)})
        if selected==original:prefix=convert(left,selected_left)
        else:
            # Use a theorem to instantiate bound case variables hygienically;
            # term substitution alone must not rename proof binders.
            choice_theorem=add('theorem',{'Theorem':dict(params=[['key',key_sort],['row',row_sort]],conditions=[],**{'from':contrib(original,'row'),'to':contrib(selected,'row')},proof=view['contribution_choice']['proof'])})
            change=lambda row:{'Use':dict(theorem=choice_theorem,arguments=[var('key'),var(row)],premises=[])}
            prefix={'Call':dict(function=view['combine'],arguments=[{'Call':dict(function=view['combine'],arguments=[{'Refl':var('total')},{'Call':dict(function=view['inverse'],arguments=[change('old')])}])},change('new')])}
        right=call(function,[var(n)for n,_ in params])
        view['row_update']=dict(function=function,proof=trans(prefix,convert(selected_left,a),{'Use':dict(theorem=theorem,arguments=args,premises=[])},convert(z,right)))
        changed+=1
    if not changed:raise ValueError('no predicate row replacement applies')
    store=Store.publish(Path(directory),list(objects.values()));package['knowledge']=store.bundle(sorted(objects))
    return package
