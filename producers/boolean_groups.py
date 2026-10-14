"""Database-defined Boolean groups and source fold factorisation.

All reductions, truth-table cases and induction steps are ordinary proof terms.
This producer is untrusted; no operator, query name or descriptor grants admission.
"""
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import normal,sub,replace,binary
from producers.representations import match
from ink_knowledge import identity
from ink_knowledge.store import entry


def prove(left,right,objects,parameters,hypotheses=(),depth=0):
    """Bounded Boolean equality with datatype cases and explicit congruence."""
    if depth>12:raise ValueError('Boolean group proof case budget')
    def simplify(t):
        value=normal(t,objects);proof=convert(t,value)
        for index,(a,b) in enumerate(hypotheses):
            a,b=normal(a,objects),normal(b,objects)
            changed=replace(value,a,b)
            if changed!=value:
                step={'Substitute':dict(variable='group_hole',context=replace(value,a,var('group_hole')),equality={'Hypothesis':index})}
                reduced=normal(changed,objects)
                proof=trans(proof,step,convert(changed,reduced));value=reduced
        return value,proof
    a,pa=simplify(left);b,pb=simplify(right)
    if a==b:return trans(pa,convert(a,b),{'Sym':pb})
    def matches(t):
        if isinstance(t,dict):
            if 'Match'in t and 'Var'in t['Match']['scrutinee']:yield t['Match']['scrutinee']['Var']
            for x in t.values():yield from matches(x)
        elif isinstance(t,list):
            for x in t:yield from matches(x)
    names=set(matches([a,b]));candidate=next(((n,s)for n,s in parameters if n in names and isinstance(s,dict)and'Data'in s),None)
    if candidate:
        name,sort=candidate;datatype=sort['Data'];cases=[]
        for i,c in enumerate(objects[datatype]['payload']['declaration']['Datatype']['constructors']):
            bindings=[f'group_case_{depth}_{i}_{j}'for j in range(len(c['fields']))]
            mapping={name:cons(datatype,i,[var(n)for n in bindings])}
            params=[(n,s)for n,s in parameters if n!=name]+[(n,sort if s=='SelfType'else s)for n,s in zip(bindings,c['fields'])]
            cases.append(dict(bindings=bindings,proof=prove(sub(a,mapping),sub(b,mapping),objects,params,[(sub(x,mapping),sub(y,mapping))for x,y in hypotheses],depth+1)))
        middle={'Cases':dict(variable=name,**{'from':a,'to':b},cases=cases)}
    else:
        types=dict(parameters)
        def boolean(t):
            if 'Bool'in t:return True
            if 'If'in t:return boolean(t['If']['on_true'])and boolean(t['If']['on_false'])
            if 'Var'in t:return types.get(t['Var'])=='Bool'
            if 'Binary'in t:return t['Binary']['op']in ('==','!=','<','>','<=','>=','&&','||')
            if 'Call'in t:return objects[t['Call']['function']]['payload']['declaration']['Function']['result']=='Bool'
            return False
        def atoms(t):
            if 'Bool'in t:return
            if 'If'in t:
                for k in ['condition','on_true','on_false']:yield from atoms(t['If'][k])
            elif 'Binary'in t and t['Binary']['op']in ('&&','||','==','!=') and boolean(t['Binary']['left'])and boolean(t['Binary']['right']):
                yield from atoms(t['Binary']['left']);yield from atoms(t['Binary']['right'])
            else:yield t
        guard=next(atoms(a),None) or next(atoms(b),None)
        if guard is None:raise ValueError('false Boolean group equation')
        branches={}
        for flag in [False,True]:
            branches['on_true'if flag else'on_false']=prove(a,b,objects,parameters,[*hypotheses,(guard,{'Bool':flag})],depth+1)
        middle={'BoolSplit':dict(condition=guard,**{'from':a,'to':b},**branches)}
    return trans(pa,middle,{'Sym':pb})


def author(subject,objects,add,spec):
    if subject['result']!='Bool' or set(spec)!={'result','zero','combine','inverse'} or spec['result']!='Bool':
        raise ValueError('Boolean group descriptor/result')
    zero=spec['zero'];rows=subject['rows'];binding=subject['bindings'][subject['root']]
    query=subject['value'];q=lambda r:sub(query,{binding:r});nil=cons(rows,0,[])
    if normal(q(nil),objects)!=zero:raise ValueError('group identity does not match empty source')
    combine=add({'Function':dict(params=[['a','Bool'],['b','Bool']],result='Bool',body=spec['combine'],recursive=None)})
    inverse=add({'Function':dict(params=[['a','Bool']],result='Bool',body=spec['inverse'],recursive=None)})
    c=lambda a,b:call(combine,[a,b]);inv=lambda a:call(inverse,[a])
    key,row,tail=var('key'),var('row'),var('tail')
    contribution=add({'Function':dict(params=[['key',subject['key']],['row',subject['row']]],result='Bool',body=normal(q(cons(rows,1,[key,row,nil])),objects),recursive=None)})
    value=lambda r:call(contribution,[key,r])
    payload=dict(declaration={'Function':dict(params=[['rows',{'Data':rows}]],result='Bool',recursive=0,body=match(var('rows'),[([],zero),(['key','row','tail'],c(value(row),{'SelfCall':[tail]}))]))})
    obj=entry('definition','first-order-inductive-equality-v1',payload,sorted({rows,contribution,combine}),parameters={'rows':{'Data':rows}},result='Bool')
    fold=identity(obj);objects[fold]=obj;total=lambda r:call(fold,[r]);node=lambda r:cons(rows,1,[key,r,tail])
    a,b,d=var('a'),var('b'),var('c');bools=[('a','Bool'),('b','Bool'),('c','Bool')]
    scalar=lambda x,y:prove(x,y,objects,bools)
    group=dict(identity=scalar(c(zero,a),a),associativity=scalar(c(c(a,b),d),c(a,c(b,d))),
        commutativity=scalar(c(a,b),c(b,a)),cancellation=scalar(c(inv(a),a),zero))
    params=[('key',subject['key']),('row',subject['row']),('tail',{'Data':rows})]
    xs=var('rows')
    theorem=add({'Theorem':dict(params=[['rows',{'Data':rows}]],conditions=[],**{'from':q(xs),'to':total(xs)},proof={'Induction':dict(variable='rows',**{'from':q(xs),'to':total(xs)},cases=[
        dict(bindings=[],proof=prove(q(nil),total(nil),objects,[])),
        dict(bindings=['key','row','tail'],proof=prove(q(node(row)),total(node(row)),objects,params,[(q(tail),total(tail))]))])})},[i for i,o in objects.items()if 'Datatype'in o['payload'].get('declaration',{})])
    actual=var(binding);factorisation=trans(convert(query,q(actual)),{'Use':dict(theorem=theorem,arguments=[actual],premises=[])})
    old=value(row);neg=inv(old)
    return dict(keep=subject['keep'],table=subject['table'],contribution=contribution,combine=combine,inverse=inverse,zero=zero,factorisation=factorisation,**group,
        insertion=prove(c(total(tail),old),total(node(row)),objects,params),
        deletion=prove(c(total(node(row)),neg),total(tail),objects,params),
        replacement=prove(c(total(node(row)),c(neg,value(var('new')))),total(node(var('new'))),objects,[*params,('new',subject['row'])]))
