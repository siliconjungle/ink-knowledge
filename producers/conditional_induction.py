"""Ordinary Boolean evidence supporting induction over valid input domains.

This is untrusted proof construction. No validity condition is admitted without
kernel replay, and no source or datatype name is recognized.
"""
from ink_knowledge.store import entry, identity

MATH='first-order-inductive-equality-v1'
TRUE={'Bool':True}
FALSE={'Bool':False}

def var(name):return {'Var':name}
def choose(condition,on_true,on_false):return {'If':dict(condition=condition,on_true=on_true,on_false=on_false)}
def convert(a,b):return {'Convert':dict(**{'from':a,'to':b})}
def trans(*proofs):
    proof=proofs[0]
    for following in proofs[1:]:proof={'Trans':[proof,following]}
    return proof
def substitute(proof,context,variable='conditional_hole'):return {'Substitute':dict(variable=variable,context=context,equality=proof)}

def boolean_library():
    a,b=var('boolean_left'),var('boolean_right');conjunction=choose(a,b,FALSE)
    hole=var('conditional_hole');selector=choose(hole,b,FALSE)
    # In the false branch, the conjunction premise contradicts the selector.
    contradiction=trans(convert(FALSE,choose(FALSE,b,FALSE)),
        {'Sym':substitute({'Hypothesis':1},selector)},{'Hypothesis':0})
    left_false=trans({'Hypothesis':1},contradiction)
    right_context=choose(hole,TRUE,b)
    right_false=trans(convert(b,choose(FALSE,TRUE,b)),
        substitute(contradiction,right_context),convert(choose(TRUE,TRUE,b),TRUE))
    right_true=trans(convert(b,choose(TRUE,b,FALSE)),
        {'Sym':substitute({'Hypothesis':1},selector)},{'Hypothesis':0})
    objects={};ids={}
    for label,goal,no,yes in [('left',a,left_false,{'Hypothesis':1}),('right',b,right_false,right_true)]:
        declaration={'Theorem':dict(params=[['boolean_left','Bool'],['boolean_right','Bool']],
            conditions=[dict(**{'from':conjunction,'to':TRUE})],**{'from':goal,'to':TRUE},
            proof={'BoolSplit':dict(condition=a,**{'from':goal,'to':TRUE},on_false=no,on_true=yes)})}
        obj=entry('theorem',MATH,dict(declaration=declaration),[],
            parameters={'boolean_left':'Bool','boolean_right':'Bool'},conditions=declaration['Theorem']['conditions'])
        ident=identity(obj);objects[ident]=obj;ids[label]=ident
    return objects,ids

def guarded_goal(goal):
    if not goal['conditions'] or any(c['to']!=TRUE for c in goal['conditions']):return None
    hole=fresh_hole(goal)
    guard=TRUE;proof={'Refl':TRUE}
    for index,condition in reversed(list(enumerate(goal['conditions']))):
        previous=guard;guard=choose(condition['from'],previous,FALSE)
        proof=trans(substitute({'Hypothesis':index},choose(var(hole),previous,FALSE),hole),
            convert(choose(TRUE,previous,FALSE),previous),proof)
    return guard,proof,choose(guard,goal['goal']['from'],goal['goal']['to'])

def apply_guarded(goal,guard,guard_proof,theorem):
    hole=fresh_hole(goal)
    context=choose(var(hole),goal['goal']['from'],goal['goal']['to'])
    return trans(convert(goal['goal']['from'],choose(TRUE,goal['goal']['from'],goal['goal']['to'])),
        {'Sym':substitute(guard_proof,context,hole)},
        {'Use':dict(theorem=theorem,arguments=[var(n) for n,_ in goal['params']],premises=[])})

def fresh_hole(goal):
    from producers.point_delta import free_variables
    occupied={n for n,_ in goal['params']}
    for equation in [*goal['conditions'],goal['goal']]:
        occupied.update(free_variables(equation['from'])|free_variables(equation['to']))
    name='conditional_hole'
    while name in occupied:name+='_'
    return name
