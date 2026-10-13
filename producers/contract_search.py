"""Bounded typed witness enumeration for arbitrary source contracts.

This is untrusted search. Clauses supply candidate terms, not an authority to
weaken the specification. Every proposed body goes through complete rechecking.
The grammar also searches named implementations and ordinary typed functions;
it is independent of privileged theorem or algorithm names.
"""
import itertools,json

def key(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'))

def mentions(value,name):
    if value=={'Var':name}:return True
    if isinstance(value,dict):return any(mentions(v,name)for v in value.values())
    if isinstance(value,list):return any(mentions(v,name)for v in value)
    return False

def nodes(value):
    if isinstance(value,dict):
        yield value
        for v in value.values():yield from nodes(v)
    elif isinstance(value,list):
        for v in value:yield from nodes(v)

def witnesses(program,spec,limit=32):
    if not 1<=limit<=256:raise ValueError('contract witness budget')
    result=spec['result'];params=spec['params'];terms=[];seen=set()
    def add(value):
        if mentions(value,'result'):return
        fingerprint=key(value)
        if fingerprint not in seen:seen.add(fingerprint);terms.append(value)
    # Exact witnesses remain first, including alternatives nested in disjunctions.
    for clause in spec['ensures']:
        for node in nodes(clause):
            binary=node.get('Binary')
            if binary and len(binary)==3:
                operation,left,right=binary
                if left=={'Var':'result'}:
                    add(right)
                    if operation=='<':add({'Binary':['-',right,{'Num':1}]})
                    if operation=='>':add({'Binary':['+',right,{'Num':1}]})
                if right=={'Var':'result'}:
                    add(left)
                    if operation=='>':add({'Binary':['-',left,{'Num':1}]})
                    if operation=='<':add({'Binary':['+',left,{'Num':1}]})
    by_type={}
    for name,ty in params:by_type.setdefault(key(ty),[]).append({'Var':name})
    for value in by_type.get(key(result),[]):add(value)
    if result=='Bool':add({'Bool':True});add({'Bool':False})
    elif result=='Unit':add('Unit')
    elif result in ('U32','U64','I32','Int'):
        add({'Num':0});add({'Num':1})
        for clause in spec['ensures']+spec['requires']:
            for node in nodes(clause):
                if set(node)=={'Num'}:add(node)
    elif isinstance(result,dict)and 'List'in result:
        add({'Call':['list',[]]})
    functions=program.get('functions',[])
    # Candidate calls use type-matching source arguments. Arity and totality,
    # contracts, captures, and every final observation are checked by the core.
    for function in functions:
        if function['name']==spec['name']or function['result']!=result:continue
        choices=[by_type.get(key(t),[])for _,t in function['params']]
        for args in itertools.islice(itertools.product(*choices),16):
            add({'Call':[function['name'],list(args)]})
    if spec['kind']is None:
        for implementation in program.get('contracts',{}).get('implementations',[]):
            if implementation['specification']==spec['name']:
                function=next((f for f in functions if f['name']==implementation['name']),None)
                if function:add(function['body'])
        for value in terms[:limit]:yield {'Pure':value}
    else:
        bodies=[{'Action':[{'Return':value}]}for value in terms]
        for implementation in program.get('contracts',{}).get('implementations',[]):
            if implementation['specification']==spec['name']and implementation.get('body'):
                bodies.append({'Action':implementation['body']})
        for body in bodies[:limit]:yield body
