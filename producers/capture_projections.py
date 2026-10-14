"""Propose general scalar projection hoisting out of repeated callbacks.

A proposal is only a typed source equality with ordinary Normalize evidence;
labels, occurrence counts and ownership hypotheses grant no rewrite authority.
"""
from producers.semantic_laws import law
from producers.definition_context28 import bind
from ink_planner.semantic_search import children,shift

SCALARS={'Bool','U32','U64','I32','F32'}
MAX_CANDIDATES=256

def root(term):
    node=term['node']
    if isinstance(node,dict)and'Free'in node:return node['Free']
    if isinstance(node,dict)and'Op'in node and node['Op'][0].startswith('field:')and len(node['Op'][1])==1:return root(node['Op'][1][0])
    return None

def specialize(subject,core):
    rows=[]
    for function in core['program']['functions']:
        body=subject['functions'].get(function['name'])
        if body is None:continue
        params={name:{'Value':ty}for name,ty in function['params']}
        fields=[]
        def visit(term,depth=0):
            node=term['node'];sort=term['sort']
            value=sort.get('Value') if isinstance(sort,dict) else None
            if depth and isinstance(value,str)and value in SCALARS and isinstance(node,dict)and'Op'in node and node['Op'][0].startswith('field:')and root(term)in params and term not in fields:fields.append(term)
            for child in children(term):visit(child,depth+int(isinstance(node,dict)and'Lambda'in node))
        visit(body)
        for number,field in enumerate(fields[:8]):
            def replace(term,depth=0):
                if term==field:return dict(sort=field['sort'],node={'Bound':depth})
                node=term['node'];items=[replace(child,depth+int(isinstance(node,dict)and'Lambda'in node))for child in children(term)]
                if isinstance(node,dict)and'Op'in node:node={'Op':[node['Op'][0],items]}
                elif isinstance(node,dict)and'Lambda'in node:node={'Lambda':items[0]}
                elif isinstance(node,dict)and'Cons'in node:node={'Cons':items}
                return dict(sort=term['sort'],node=node)
            abstraction=dict(sort={'Arrow':[field['sort'],body['sort']]},node={'Lambda':replace(shift(body,1))})
            target=dict(sort=body['sort'],node={'Op':['apply',[abstraction,field]]})
            try:proposal=bind(law(params,body,target),core,subject,[function['name']])
            except(ValueError,KeyError):continue
            rows.append(('hoist_projection/'+function['name']+'/'+str(number),proposal))
            if len(rows)>=MAX_CANDIDATES:return rows
    return rows
