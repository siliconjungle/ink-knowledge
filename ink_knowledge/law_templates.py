"""Untrusted, snapshot-owned type instantiation of proof templates.

Templates are authoring data, not kernel theorems. Only instantiated canonical
laws and their ordinary proof closures can authorise an executable rewrite.
"""
import copy
from .store import semantic_entry,identity
SEMANTICS='ink-semantic-law-template-v1'

def substitute_types(value,bindings):
    if isinstance(value,dict):
        if set(value)=={'Named'} and isinstance(value['Named'],str) and value['Named'].startswith('$'):
            return copy.deepcopy(bindings[value['Named'][1:]])
        return {k:substitute_types(v,bindings)for k,v in value.items()}
    if isinstance(value,list):return [substitute_types(v,bindings)for v in value]
    return copy.deepcopy(value)

def unify_type(pattern,actual,names,bindings):
    if isinstance(pattern,dict) and set(pattern)=={'Named'} and pattern['Named'] in {'$'+n for n in names}:
        n=pattern['Named'][1:]
        if n in bindings:return bindings[n]==actual
        bindings[n]=copy.deepcopy(actual);return True
    if type(pattern)!=type(actual):return False
    if isinstance(pattern,dict):return set(pattern)==set(actual)and all(unify_type(v,actual[k],names,bindings)for k,v in pattern.items())
    if isinstance(pattern,list):return len(pattern)==len(actual)and all(unify_type(a,b,names,bindings)for a,b in zip(pattern,actual))
    return pattern==actual

def infer(pattern,actual,params,names,bindings):
    if not unify_type(pattern['sort'],actual['sort'],names,bindings):return False
    p,a=pattern['node'],actual['node']
    if isinstance(p,dict)and p.get('Free')in params:return True
    if type(p)!=type(a):return False
    from ink_planner.semantic_search import children
    if not isinstance(p,dict):return p==a
    if set(p)!=set(a):return False
    if 'Op'in p and p['Op'][0]!=a['Op'][0]:return False
    pc,ac=children(pattern),children(actual)
    if not pc:return p==a
    return len(pc)==len(ac)and all(infer(x,y,params,names,bindings)for x,y in zip(pc,ac))

def generate(store,subject,core):
    from .template_matching import TemplateSites
    from .proposals import nominal_types
    from producers.definition_context28 import bind
    templates={};after=None
    while True:
        page=store.query(kind='definition',semantics=SEMANTICS,after=after,limit=64)
        for ident in page:
            payload=store.object(ident)['payload']
            if set(payload)!={'type_parameters','law','dependencies'}:raise ValueError('law template fields')
            names=payload['type_parameters']
            if not isinstance(names,list)or not 1<=len(names)<=8 or len(set(names))!=len(names)or any(not isinstance(n,str)or not n.isidentifier()for n in names):raise ValueError('law template type parameters')
            if not isinstance(payload['dependencies'],dict)or len(payload['dependencies'])>64:raise ValueError('law template dependency budget')
            templates[ident]=payload
        if len(templates)>4096:raise ValueError('law template count budget')
        if len(page)<64:break
        after=page[-1]
    objects={};receipts=[];sites=TemplateSites(subject)
    def instantiate(payload,bindings,active):
        if len(active)>16:raise ValueError('law template dependency depth')
        candidate=substitute_types(payload['law'],bindings);dependencies={}
        for label,dep in payload['dependencies'].items():
            if not isinstance(label,str)or not label.startswith('$')or dep in active:raise ValueError('law template dependency cycle or label')
            if dep not in templates:raise ValueError('law template dependency absent from snapshot')
            dependencies[label]=instantiate(templates[dep],bindings,active|{dep})
        def references(v):
            if isinstance(v,dict):return {k:dependencies[x]if k=='law' and isinstance(x,str) and x in dependencies else references(x)for k,x in v.items()}
            if isinstance(v,list):return [references(x)for x in v]
            return v
        candidate=references(candidate);candidate['dependencies']=sorted(set(dependencies.values()))
        if nominal_types(candidate):candidate=bind(candidate,core,subject)
        obj=semantic_entry(candidate);ident=identity(obj);objects[ident]=obj
        if len(objects)>1024:raise ValueError('instantiated law template budget')
        return ident
    for ident,payload in sorted(templates.items()):
        instances=set()
        before=sites.attempts
        for _,_,_,bindings in sites.matches(payload['law']['from'],payload['law']['params'],payload['type_parameters']):
            instances.add(instantiate(payload,bindings,{ident}))
        receipts.append(dict(template=ident,instances=len(instances),inference_attempts=sites.attempts-before,subject_nodes=len(sites.sites)))
    return objects,receipts
