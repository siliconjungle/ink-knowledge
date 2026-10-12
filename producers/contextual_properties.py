"""Discover observations directly from arbitrary typed theorem contexts.
No list of privileged property names: a published law can bring new refinements,
invariants, projections or summaries without adding a compiler recognition case.
"""
import copy,itertools,json,tempfile
from pathlib import Path
from ink_knowledge import Store,canonical
from producers.planning_recipes import row,compiler

def contextual_queries(law,body,parameters,variable="__subject",limit=64):
    from ink_planner.semantic_search import children,match,substitute,replace
    # A source body must not acquire a theorem's local binder. Ignore holes under
    # lambdas; matcher checks binder hygiene inside the selected fragment.
    def positions(t,path=()):
        yield path,t
        if isinstance(t['node'],dict) and 'Lambda' in t['node']:return
        for i,c in enumerate(children(t)):yield from positions(c,path+(i,))
    remaining=limit
    for path,fragment in positions(law['from']):
        bindings={}
        if not match(fragment,body,law['params'],bindings):continue
        missing=sorted(set(law['params'])-set(bindings))
        choices=[[dict(sort=s,node={'Free':n}) for n,s in sorted(parameters.items()) if s==law['params'][k]] for k in missing]
        for values in itertools.product(*choices):
            if remaining<=0:return
            args=dict(bindings,**dict(zip(missing,values)));remaining-=1
            context=replace(substitute(law['from'],args),path,dict(sort=body['sort'],node={'Free':variable}))
            yield context,substitute(law['to'],args),args

def propose(context):
    from ink_planner.semantic_search import condition_proof,substitute,discovery_objects,selection_roots
    store=Store(context['knowledge_root'],Path(context['knowledge_root'])/'store/snapshots'/f"{context['knowledge_snapshot']}.json" if context.get('knowledge_snapshot') else None)
    with tempfile.TemporaryDirectory(prefix='ink-context-properties-') as tmp:
        core=Path(tmp)/'core.json';out=Path(tmp)/'terms.json';core.write_bytes(canonical(context['core']))
        compiler(context,'emit-semantic',core,'--core','-o',out);subjects=json.loads(out.read_bytes())['functions']
        signatures={f['name']:f for f in context['core']['program']['functions']};after=None
        while True:
            page=store.query(kind='rewrite',semantics='ink-conditional-laws-v1',after=after,limit=256)
            for ident in page:
                law=store.object(ident)['payload']
                for name,body in subjects.items():
                    if name not in signatures:continue
                    params={n:{'Value':s} for n,s in signatures[name]['params']}
                    variable='__subject'
                    while variable in params:variable+='_' 
                    for observation,target,args in contextual_queries(law,body,params,variable):
                        if observation['node']=={'Free':variable}:continue # ordinary value probe already covers this
                        objects=discovery_objects(store,[ident]);catalogue=dict(objects={i:o['payload'] for i,o in objects.items() if o['kind']=='rewrite'})
                        premises=[condition_proof(dict(**{'from':substitute(c['from'],args),'to':substitute(c['to'],args)}),catalogue) for c in law['conditions']]
                        proof={'Use':dict(law=ident,arguments=args,premises=premises)}
                        roots=selection_roots([dict(law=ident,premises=premises)])
                        packet=dict(schema=1,semantics='ink-source-properties-v1',input_core_sha256=context['source'],knowledge=store.bundle(roots),facts=[dict(function=name,context=observation,subject_variable=variable,value=target,proof=proof)])
                        yield row('properties',packet,'context/'+name+'/'+ident)
            if len(page)<256:return
            after=page[-1]
