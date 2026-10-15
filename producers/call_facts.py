"""Bounded, untrusted call-body summaries for unsigned fact discovery.

Expansions are proposals, never assumptions. Exact definition contexts and a
whole-function proof must replay independently before an expanded fact is used.
"""
import copy
from ink_knowledge import identity
from ink_planner.semantic_search import children,set_child,substitute
from .beta_specialization15 import beta_normalize


def expand(source,core,subject,*,max_nodes=4096,max_calls=128,max_depth=32):
    functions={f['name']:f for f in core['program']['functions']}
    remaining=[max_nodes];calls=[0];summaries={};active=set();used={}
    def scalar(sort):
        if not isinstance(sort,dict):return False
        if set(sort)=={'Value'}:return sort['Value']in ('Bool','U32','U64')if isinstance(sort['Value'],str)else False
        return set(sort)=={'Arrow'}and all(scalar(s)for s in sort['Arrow'])
    def walk(t,depth):
        remaining[0]-=1
        if remaining[0]<0 or depth>max_depth:raise ValueError('call fact expansion budget')
        if not scalar(t['sort']):raise ValueError('call facts support only unsigned words and Bool')
        node=t['node'];out=copy.deepcopy(t)
        for i,child in enumerate(children(t)):out=set_child(out,i,walk(child,depth+1))
        op=node.get('Op')if isinstance(node,dict)else None
        if op and op[0].startswith('call:')and op[0][5:]in functions:
            name=op[0][5:];f=functions[name];args=out['node']['Op'][1]
            if name in active:raise ValueError('recursive call summaries are unknown')
            if name not in subject['functions']:raise ValueError('callee outside semantic fact domain: '+name)
            if len(args)!=len(f['params']):raise ValueError('call fact arity')
            calls[0]+=1
            if calls[0]>max_calls:raise ValueError('call fact count budget')
            # Cache parameterized bodies locally, keyed by their exact source
            # signature and semantic definition. Caller branch facts stay out.
            key=identity([f['params'],f['result'],subject['functions'][name]])
            if key not in summaries:
                active.add(name)
                try:summaries[key]=walk(subject['functions'][name],depth+1)
                finally:active.remove(name)
            # Substitution is binder-safe; every copy is charged by a subsequent
            # bounded beta pass and final traversal before analysis.
            arguments=dict(zip([n for n,_ in f['params']],args));used[name]=key
            def size(t):
                pending=[t];count=0
                while pending:
                    count+=1
                    if count>max_nodes:raise ValueError('call argument size budget')
                    pending.extend(children(pending.pop()))
                return count
            sizes={n:size(a)for n,a in arguments.items()};pending=[summaries[key]];estimate=0
            while pending:
                child=pending.pop();free=child['node'].get('Free')if isinstance(child['node'],dict)else None
                estimate+=sizes.get(free,1)
                if estimate>max_nodes:raise ValueError('call substitution size budget')
                if free not in arguments:pending.extend(children(child))
            remaining[0]-=estimate
            if remaining[0]<0:raise ValueError('call substitution work budget')
            out=substitute(summaries[key],arguments)
        return out
    result=beta_normalize(walk(source,0),budget=max_nodes)
    pending=[(result,0)];count=0
    while pending:
        t,depth=pending.pop();count+=1
        if count>max_nodes or depth>max_depth:raise ValueError('expanded call fact size budget')
        pending.extend((c,depth+1)for c in children(t))
    return result,dict(expanded_calls=calls[0],summary_count=len(summaries),expanded_nodes=count,
        definitions=dict(sorted(used.items())))
