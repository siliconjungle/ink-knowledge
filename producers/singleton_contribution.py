"""Author a scalar singleton contribution through explicit Boolean cases.

The surrounding aggregate induction rechecks this body against the unchanged
source pipeline. This only distributes total mathematical computation; source
order/effects are bound elsewhere and no producer result grants authority.
"""
from point_delta import normal,replace,choice,free_variables


def specialize(term,objects,parameter,depth=0):
    if depth>8:raise ValueError('singleton contribution branch budget')
    reduced=normal(term,objects)
    def guard(t):
        if isinstance(t,dict):
            if 'If'in t:
                candidate=t['If']['condition']
                if free_variables(candidate)<={parameter}:return candidate
            for value in t.values():
                found=guard(value)
                if found is not None:return found
        elif isinstance(t,list):
            for value in t:
                found=guard(value)
                if found is not None:return found
        return None
    condition=guard(reduced)
    if condition is None:return reduced
    return choice(condition,specialize(replace(reduced,condition,{'Bool':True}),objects,parameter,depth+1),specialize(replace(reduced,condition,{'Bool':False}),objects,parameter,depth+1))
