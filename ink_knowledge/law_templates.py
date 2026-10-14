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
    from .higher_patterns import match
    return match(pattern,actual,params,names,bindings,{})

def generate(store,subject,core):
    from .template_matching import TemplateSites
    from .proposals import nominal_types
    from producers.definition_context28 import bind
    from .template_index import candidates
    sites=TemplateSites(subject)
    templates={};selected=candidates(store,subject,SEMANTICS,sites=sites);pending=list(selected)
    while pending:
        page=pending[:64];pending=pending[64:]
        for ident in page:
            if ident in templates:continue
            obj=store.object(ident)
            if obj['kind']!='definition' or obj['semantics']!=SEMANTICS:raise ValueError('law template dependency role')
            payload=obj['payload']
            if set(payload)!={'type_parameters','law','dependencies'}:raise ValueError('law template fields')
            names=payload['type_parameters']
            if not isinstance(names,list)or not 1<=len(names)<=8 or len(set(names))!=len(names)or any(not isinstance(n,str)or not n.isidentifier()for n in names):raise ValueError('law template type parameters')
            if not isinstance(payload['dependencies'],dict)or len(payload['dependencies'])>64:raise ValueError('law template dependency budget')
            templates[ident]=payload
            pending.extend(dep for dep in payload['dependencies'].values() if dep not in templates)
        if len(templates)>4096:raise ValueError('law template count budget')
    objects={};receipts=[];instances_cache={};cache_hits=0;adapter_cache={};adapter_hits=0
    def instantiate(template_id,bindings,active):
        nonlocal cache_hits
        from .store import canonical
        cache_key=(template_id,canonical(bindings))
        cached=instances_cache.get(cache_key)
        if cached is not None:
            ident,height=cached
            if len(active)+height>16:raise ValueError('law template dependency depth')
            cache_hits+=1
            return ident,height
        payload=templates[template_id]
        if len(active)>16:raise ValueError('law template dependency depth')
        candidate=substitute_types(payload['law'],bindings);dependencies={};height=0
        for label,dep in payload['dependencies'].items():
            if not isinstance(label,str)or not label.startswith('$')or dep in active:raise ValueError('law template dependency cycle or label')
            if dep not in templates:raise ValueError('law template dependency absent from snapshot')
            dependencies[label],child_height=instantiate(dep,bindings,active|{dep})
            height=max(height,child_height+1)
        def references(v):
            if isinstance(v,dict):return {k:dependencies[x]if k=='law' and isinstance(x,str) and x in dependencies else references(x)for k,x in v.items()}
            if isinstance(v,list):return [references(x)for x in v]
            return v
        candidate=references(candidate);candidate['dependencies']=sorted(set(dependencies.values()))
        if nominal_types(candidate):candidate=bind(candidate,core,subject)
        obj=semantic_entry(candidate);ident=identity(obj);objects[ident]=obj
        if len(objects)>1024:raise ValueError('instantiated law template budget')
        instances_cache[cache_key]=(ident,height)
        return ident,height
    for ident in selected:
        payload=templates[ident]
        instances=set();produced=set()
        before=sites.attempts;hits_before=cache_hits;adapters_before=adapter_hits
        for _,_,target,bindings in sites.matches(payload['law']['from'],payload['law']['params'],payload['type_parameters']):
            base_id,_=instantiate(ident,bindings,{ident});instances.add(base_id);produced.add(base_id)
            base=objects[base_id]['payload']
            from ink_planner.semantic_search import match,substitute,children
            args={}
            if match(base['from'],target,base['params'],args):continue
            from .store import canonical
            adapter_key=(base_id,canonical(target))
            if adapter_key in adapter_cache:
                produced.add(adapter_cache[adapter_key]);adapter_hits+=1
                continue
            from .higher_patterns import match as higher_match
            args={}
            if not higher_match(base['from'],target,base['params'],[],{},args)or set(args)!=set(base['params']):continue
            params={}
            def free(t,depth=0):
                node=t['node']
                if isinstance(node,dict):
                    if 'Bound'in node and node['Bound']>=depth:raise ValueError('open adapter site')
                    if 'Free'in node:
                        name=node['Free']
                        if name in params and params[name]!=t['sort']:raise ValueError('adapter free sort conflict')
                        params[name]=t['sort']
                for child in children(t):free(child,depth+int(isinstance(node,dict)and 'Lambda'in node))
            try:
                free(target)
                for arg in args.values():free(arg)
            except ValueError:continue
            # Exact source endpoint -> beta-expanded universal instance -> target.
            # The adapter is ordinary proof data, not a new checker match mode.
            middle=substitute(base['from'],args)
            proof={'Trans':dict(middle=middle,left='Normalize',right={'Use':dict(law=base_id,arguments=args,premises=[{'Hypothesis':i} for i in range(len(base['conditions']))])})}
            # Keep each instantiated premise as an adapter obligation. Its
            # Hypothesis proof above is scoped to this law, never caller trust.
            conditions=[{side:substitute(condition[side],args)for side in ('from','to')}for condition in base['conditions']]
            candidate=dict(semantics='ink-conditional-laws-v1',params=params,conditions=conditions,**{'from':target,'to':substitute(base['to'],args)},proof=proof,dependencies=[base_id])
            if nominal_types(candidate):candidate=bind(candidate,core,subject)
            obj=semantic_entry(candidate);adapter_id=identity(obj);objects[adapter_id]=obj;produced.add(adapter_id)
            if len(objects)>1024:raise ValueError('instantiated law template budget')
            adapter_cache[adapter_key]=adapter_id
        receipts.append(dict(template=ident,laws=sorted(produced),instances=len(instances),inference_attempts=sites.attempts-before,subject_nodes=len(sites.sites),instantiation_cache_hits=cache_hits-hits_before,adapter_cache_hits=adapter_hits-adapters_before))
    return objects,receipts
