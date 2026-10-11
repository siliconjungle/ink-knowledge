"""Untrusted parameter-key repair and source-bound field preservation tactics.

Cached queries may project a fixed point lookup through a pure total expression.
Every different-key, same-key and field-preserving proposal carries ordinary
closed proofs; the complete source observation remains the admission boundary.
"""
import json
from producers.point_delta import (var,call,cons,choice,binary,match,sub,replace,normal,lift,equality)
from producers.action_replacement import convert,trans,alpha_normal
from producers.cache_maintenance import variables

def free(term,bound=frozenset()):
    if isinstance(term,list):return set().union(*(free(t,bound)for t in term))
    if not isinstance(term,dict):return set()
    if 'Var'in term:return set()if term['Var']in bound else{term['Var']}
    if 'Match'in term:
        m=term['Match'];return free(m['scrutinee'],bound)|set().union(*(free(b['body'],bound|set(b['bindings']))for b in m['branches']))
    return set().union(*(free(t,bound)for t in term.values()))

_general=None
def setup(model,cache,add,objects):
    global _general
    from producers.state_calculus import build,CanonicalLibrary
    reply=cache['case']['normal']['Construct']['arguments'][0]
    found=[]
    def walk(term):
        if isinstance(term,list):
            for t in term:walk(t)
        elif isinstance(term,dict):
            c=term.get('Call',{});args=c.get('arguments',[])
            if len(args)==2 and 'U64'in args[1]and args[0].get('Var')in cache['case']['bindings']and any(t['get']==c.get('function')for t in model['tables']):found.append(term)
            for t in term.values():walk(t)
    walk(reply)
    if not found or any(t!=found[0]for t in found):raise ValueError('point repair requires one fixed-u64 lookup')
    lookup=found[0];f=lookup['Call'];initial,q=f['arguments'];table=next(t for t in model['tables']if t['get']==f['function']);index=cache['case']['bindings'].index(initial['Var'])
    d=table['datatype'];get=table['get'];option=objects[get]['payload']['declaration']['Function']['result']['Data'];OS={'Data':option}
    row_sort=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    result_sort=objects[cache['result']['Data']]['payload']['declaration']['Datatype']['constructors'][0]['fields'][0]
    old_name='point_option'
    while old_name in variables(reply):old_name+='_'
    projected=replace(reply,lookup,var(old_name))
    if free(projected)-{old_name}:raise ValueError('point projection has additional state dependencies')
    carriers=[i for i,e in model['objects'].items()if 'Datatype'in e['payload'].get('declaration',{})]
    def emit(declaration):return add(declaration,carriers)
    projection=emit({'Function':dict(params=[[old_name,OS]],result=result_sort,recursive=None,body=projected)})
    P=lambda old:call(projection,[old]);G=lambda rows:call(get,[rows,q]);Q=lambda rows:P(G(rows))
    none=cons(option,0,[]);some=lambda row:cons(option,1,[row]);identity=reply==lookup
    present=emit({'Function':dict(params=[['old',OS],['new',row_sort]],result=OS,recursive=None,body=match(var('old'),[([],none),(['previous'],some(var('new')))]))})
    if _general is None:_general=build(CanonicalLibrary())
    lib=_general;n=lib.names
    pending=[n[name]for name in ('lookup_general_remove','lookup_general_replace','word_equal_from_guard','WordRows','RowOption','get','remove','replace','replace_present')]
    while pending:
        i=pending.pop()
        if i in objects:continue
        e=lib.objects[i];objects[i]=e;pending.extend(e['dependencies'])
    definitions={n['WordRows']:d,n['RowOption']:option,n['get']:get,n['remove']:table['remove'],n['replace']:table['replace'],n['replace_present']:present}
    carriers.extend(definitions)
    def instance(name,args):return {'Instance':dict(theorem=n[name],sorts={n['StateRow']:row_sort},functions={},definitions=definitions,assumptions={},arguments=args,premises=[])}
    rows,key,new=map(var,('point_rows','point_key','point_new'));guard=binary('==',q,key)
    updates={}
    for operation in ('remove','replace'):
        args=[rows,key]+([new]if operation=='replace'else[])
        left=Q(call(table[operation],args));changed=none if operation=='remove'else call(present,[G(rows),new])
        middle=P(choice(guard,changed,G(rows)));right=choice(guard,P(changed),Q(rows))
        first=lift(instance('lookup_general_'+operation,[rows,key,q]+([new]if operation=='replace'else[])),P(var('delta_hole')))
        branches={}
        for flag in (False,True):branches['on_true'if flag else'on_false']=equality(middle,right,objects,facts=[(guard,{'Bool':flag},0)])
        proof=trans(first,{'BoolSplit':dict(condition=guard,**{'from':middle,'to':right},**branches)})
        updates[operation]=emit({'Theorem':dict(params=[['point_rows',{'Data':d}],['point_key','U64']]+([['point_new',row_sort]]if operation=='replace'else[]),conditions=[],**{'from':left,'to':right},proof=proof)})
    fields=objects[model['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields'];current_env={};preservation={}
    def remember_bindings(bindings):current_env.update(dict(zip(bindings,fields)))
    def preserving(rows,key,new):
        """Try actual row constructors; failed authoring retains general repair."""
        old=var(old_name);at_key=call(get,[rows,key]);new=normal(new,objects);template=replace(new,at_key,old)
        if template==new:return None
        left=P(call(present,[old,template]));right=P(old)
        captures=sorted((free(left)|free(right))-{old_name})
        if any(c not in current_env for c in captures):return None
        params=[[old_name,OS]]+[[c,current_env[c]]for c in captures]
        fingerprint=json.dumps([params,left,right],sort_keys=True)
        if fingerprint in preservation:return preservation[fingerprint],captures
        old_row='point_old_row'
        while old_row in current_env or old_row==old_name:old_row+='_'
        def one(option_value):return sub(left,{old_name:option_value}),sub(right,{old_name:option_value})
        a,z=one(none)
        if alpha_normal(normal(a,objects))!=alpha_normal(normal(z,objects)):return None
        nil_proof=convert(a,z);a,z=one(some(var(old_row)))
        if isinstance(row_sort,dict)and 'Datatype'in objects[row_sort['Data']]['payload']['declaration']:
            datatype=row_sort['Data'];constructors=objects[datatype]['payload']['declaration']['Datatype']['constructors'];case_proofs=[]
            for tag,constructor in enumerate(constructors):
                bindings=[]
                for i,_ in enumerate(constructor['fields']):
                    name='point_field_'+str(i)
                    while name in current_env or name in captures or name in (old_name,old_row):name+='_'
                    bindings.append(name)
                row=cons(datatype,tag,[var(s)for s in bindings]);aa,zz=sub(a,{old_row:row}),sub(z,{old_row:row})
                if alpha_normal(normal(aa,objects))!=alpha_normal(normal(zz,objects)):return None
                case_proofs.append(dict(bindings=bindings,proof=convert(aa,zz)))
            row_proof={'Cases':dict(variable=old_row,**{'from':a,'to':z},cases=case_proofs)}
        else:
            if alpha_normal(normal(a,objects))!=alpha_normal(normal(z,objects)):return None
            row_proof=convert(a,z)
        proof={'Cases':dict(variable=old_name,**{'from':left,'to':right},cases=[dict(bindings=[],proof=nil_proof),dict(bindings=[old_row],proof=row_proof)])}
        lemma=emit({'Theorem':dict(params=params,conditions=[],**{'from':left,'to':right},proof=proof)})
        preservation[fingerprint]=lemma;return lemma,captures
    def preserved_step(rows,key,new,bindings):
        remember_bindings(bindings);found=preserving(rows,key,new)
        if found is None:return None
        lemma,captures=found;guard=binary('==',q,key)
        expr=P(call(present,[G(rows),new]));at_key=call(get,[rows,key])
        known=normal(guard,objects).get('Bool')
        guard_proof=convert(guard,{'Bool':True})if known is True else {'Hypothesis':0}
        reflection={'Use':dict(theorem=n['word_equal_from_guard'],arguments=[q,key],premises=[guard_proof])}
        yes=trans(lift(reflection,P(call(present,[call(get,[rows,var('delta_hole')]),new]))),{'Use':dict(theorem=lemma,arguments=[at_key]+[var(c)for c in captures],premises=[])},{'Sym':lift(reflection,P(call(get,[rows,var('delta_hole')])) )})
        middle=choice(guard,expr,Q(rows));target=Q(rows)
        args=[rows,key,new]
        first={'Use':dict(theorem=updates['replace'],arguments=args,premises=[])}
        # A literal key comparison has only one reachable branch. Do not ask
        # the equality tactic to derive an unreachable False premise after
        # computation has already reduced the comparison to True.
        if known is True:return trans(first,convert(middle,expr),yes)
        if known is False:return trans(first,convert(middle,target))
        yes=trans(equality(middle,expr,objects,facts=[(guard,{'Bool':True},0)]),yes)
        no=equality(middle,target,objects,facts=[(guard,{'Bool':False},0)])
        return trans(first,{'BoolSplit':dict(condition=guard,**{'from':middle,'to':target},on_false=no,on_true=yes)})
    def recipe(root,old,bindings):
        remember_bindings(bindings)
        if root==var(bindings[index]):return old
        c=root.get('Call',{});args=c.get('arguments',[])
        operation=next((op for op in ('remove','replace')if table[op]==c.get('function')),None)
        if operation is None:raise ValueError('point repair mutation refresh required')
        prior=recipe(args[0],old,bindings);guard=binary('==',q,args[1])
        if operation=='remove':return normal(choice(guard,P(none),prior),objects)
        if preserving(args[0],args[1],args[2])is not None:return prior
        before=prior if identity else G(args[0])
        changed=call(present,[before,args[2]])
        return normal(choice(guard,P(changed),prior),objects)
    def action(sa):
        current_env.clear();current_env.update(dict(sa['params'][1:]));remember_bindings(sa['case']['bindings']);old=var('cached_reply');initial=var(sa['case']['bindings'][index])
        def predict(term):
            if 'If'in term:
                x=term['If'];yes,no=predict(x['on_true']),predict(x['on_false'])
                if yes==no:return yes
                condition=replace(x['condition'],G(initial),old)if identity else x['condition']
                return choice(condition,yes,no)
            o=term['Construct']
            if o['constructor']!=0 or o['arguments'][1]!={'Bool':True}:return old
            return recipe(o['arguments'][3]['Construct']['arguments'][index],old,sa['case']['bindings'])
        try:return predict(sa['case']['normal'])
        except(ValueError,KeyError):return None
    def query_equality(root,bindings):
        if root==var(bindings[index]):return {'Refl':Q(root)}
        c=root['Call'];args=c['arguments'];operation=next(op for op in ('remove','replace')if table[op]==c['function'])
        if operation=='replace':
            proof=preserved_step(*args,bindings)
            if proof is not None:return trans(proof,query_equality(args[0],bindings))
        proof={'Use':dict(theorem=updates[operation],arguments=args,premises=[])}
        guard=binary('==',q,args[1]);prior=recipe(args[0],Q(var(bindings[index])),bindings)
        changed=P(none)if operation=='remove'else P(call(present,[G(args[0]),args[2]]))
        if operation=='replace'and identity:
            context=choice(guard,P(call(present,[var('delta_hole'),args[2]])),var('delta_hole'))
        else:context=choice(guard,changed,var('delta_hole'))
        target=recipe(root,Q(var(bindings[index])),bindings)
        return trans(proof,lift(query_equality(args[0],bindings),context),convert(choice(guard,P(call(present,[prior,args[2]]))if operation=='replace'and identity else changed,prior),target))
    def equality_entry(root,bindings):
        # A source action already has branch premises. Factor the independent
        # point proof so its local BoolSplit indices cannot capture those.
        remember_bindings(bindings)
        left=Q(root);right=recipe(root,Q(var(bindings[index])),bindings)
        names=sorted(free(left)|free(right));params=[[name,current_env[name]]for name in names]
        lemma=emit({'Theorem':dict(params=params,conditions=[],**{'from':left,'to':right},proof=query_equality(root,bindings))})
        return {'Use':dict(theorem=lemma,arguments=[var(name)for name in names],premises=[])}
    return dict(action=action,recipe=recipe,equality=equality_entry,index=index,get=get,q=q,option=option)
