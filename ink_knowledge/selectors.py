"""Bounded declarative selectors for untrusted implementation proposals.

Selectors inspect data; they cannot execute code, prove facts or admit a plan.
Missing paths conservatively decline the match. Actual capability checking is
performed by the compiler against the exact source and reachable definitions.
"""
class Missing(Exception):pass

def evaluate(expression, subject, node_limit=4096):
    remaining=[node_limit]
    def run(e,env,depth=0):
        remaining[0]-=1
        if remaining[0]<0 or depth>64:raise ValueError('selector budget')
        if not isinstance(e,dict)or len(e)!=1:raise ValueError('selector expression')
        op,args=next(iter(e.items()))
        sub=lambda x:run(x,env,depth+1)
        if op=='literal':return args
        if op=='path':
            if not isinstance(args,list)or len(args)>32:raise ValueError('selector path')
            value=env
            for key in args:
                if isinstance(value,dict)and isinstance(key,str)and key in value:value=value[key]
                elif isinstance(value,list)and type(key)is int and -len(value)<=key<len(value):value=value[key]
                else:raise Missing()
            return value
        if op in {'all','count'}:
            if not isinstance(args,list)or len(args)!=2:raise ValueError('selector quantifier')
            values=sub(args[0])
            if not isinstance(values,list)or len(values)>4096:raise ValueError('selector list budget')
            matches=[run(args[1],dict(env,item=v),depth+1) for v in values]
            if any(type(v)is not bool for v in matches):raise ValueError('selector predicate type')
            return all(matches) if op=='all' else sum(matches)
        if op=='length':
            value=sub(args)
            if not isinstance(value,(list,dict,str)):raise ValueError('selector length type')
            return len(value)
        if not isinstance(args,list):raise ValueError('selector arguments')
        if op in {'and','or'}:
            for arg in args:
                value=sub(arg)
                if type(value)is not bool:raise ValueError('selector Boolean type')
                if op=='and'and not value:return False
                if op=='or'and value:return True
            return op=='and'
        values=[sub(x)for x in args]
        if op=='slice'and len(values)==3 and isinstance(values[0],list)and all(type(x)is int for x in values[1:]):return values[0][values[1]:values[2]]
        if op=='has'and len(values)==2 and isinstance(values[1],str):return isinstance(values[0],dict)and values[1]in values[0]
        if op=='eq'and len(values)==2:return values[0]==values[1]
        if op=='in'and len(values)==2 and isinstance(values[1],list):return values[0]in values[1]
        if op in {'le','ge'}and len(values)==2 and all(type(x)is int for x in values):return values[0]<=values[1]if op=='le'else values[0]>=values[1]
        raise ValueError('unknown or ill-typed selector operation: '+op)
    try:return run(expression,dict(subject=subject))
    except Missing:return False

def matches(expression,subject):
    result=evaluate(expression,subject)
    if type(result)is not bool:raise ValueError('selector result must be Boolean')
    return result
