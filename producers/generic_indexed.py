"""Compose typed indexed roots and checked query summaries across whole actions.

The checker receives ordinary definitions and full observation/codec obligations;
this producer is untrusted and has no application-name or field-name whitelist.
"""
import argparse,json,os,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,identity,canonical
from ink_knowledge.store import entry,read
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import match,sub,lift
from producers.representations import refs,REP,MATH
from producers.indexed_aggregate import definitions
from producers.generic_aggregates import factory
from producers.equational import Tactic,factor

def generate(model,directory, *, batching=True):
    objects=dict(model['objects']);layouts={};allrules=[];opaque=[];names={};discovery=[]
    for index,table in enumerate(model['tables']):
        if table['datatype'] in layouts:continue
        augmented={**model,'objects':objects};defs,roles=definitions(augmented,table_index=index,aggregate_factory=factory,layout_only=True);objects.update(defs)
        aggregates=roles.pop('_aggregates');layouts[table['datatype']]=dict(table=table,roles=roles,queries=aggregates[0]['queries']);opaque+=aggregates[0].get('opaque',[])
        names.update({'table-'+str(index)+'/'+k:v for k,v in roles.items()})
    def add(decl):
        body=next(iter(decl.values()));dependencies=refs(decl)
        if 'Datatype' not in decl:
            pending=list(dependencies);seen=set()
            while pending:
                ident=pending.pop()
                if ident in seen:continue
                seen.add(ident);d=objects.get(ident,{}).get('payload',{}).get('declaration',{})
                if 'Datatype' in d:dependencies.add(ident);pending+=list(refs(d))
                else:
                    for kind in ['Function','Theorem','AbstractFunction']:
                        if kind in d:pending+=list(refs([d[kind].get('params',[]),d[kind].get('result')]))
        e=entry('theorem' if 'Theorem' in decl else 'definition',MATH,{'declaration':decl},dependencies,parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]));ident=identity(e);objects[ident]=e;return ident
    def fun(params,result,body,recursive=None):return add({'Function':dict(params=params,result=result,body=body,recursive=recursive)})
    def law(params,a,z,p,conditions=()):return add({'Theorem':dict(params=params,conditions=list(conditions),**{'from':a,'to':z},proof=p)})
    def use(ident,args,premises=()):return {'Use':dict(theorem=ident,arguments=args,premises=list(premises))}
    def induction(variable,a,z,bindings,proof):return {'Induction':dict(variable=variable,**{'from':a,'to':z},cases=[dict(bindings=bindings,proof=proof)])}
    for layout in layouts.values():
        t,n=layout['table'],layout['roles'];T={'Data':n['tree']};tree,key=var('bridge_tree'),var('bridge_key');fix=lambda x:call(n['repair'],[x]);decode=lambda x:call(n['decode'],[x]);valid={'from':fix(tree),'to':tree}
        allrules += [n['repair_idempotent'],n['repair_preserves_rows']]
        functions={}
        for op in ['get','insert','replace','remove']:
            rest=[['bridge_key',objects[t['get']]['payload']['declaration']['Function']['params'][1][1]]]+([['bridge_row',objects[t['replace']]['payload']['declaration']['Function']['params'][2][1]]] if op in ['insert','replace'] else [])
            args=[var(x) for x,_ in rest];f=n['lookup' if op=='get' else op];functions[op]=f
            a=call(f,[tree,*args]);z=call(t[op],[decode(tree),*args]);left=a if op=='get' else decode(a)
            p=trans(lift({'Sym':{'Hypothesis':0}},call(f,[var('delta_hole'),*args]) if op=='get' else decode(call(f,[var('delta_hole'),*args]))),use(n['indexed_'+('lookup' if op=='get' else op)+'_preserves_rows'],[tree,*args]))
            if op=='get':p=trans(p,use(n['lookup_preserves_rows'],[tree,*args]))
            allrules.append(law([['bridge_tree',T],*rest],left,z,p,[valid]))
            if op!='get':
                a=fix(call(f,[tree,*args]));z=call(f,[tree,*args])
                p=trans(lift({'Sym':{'Hypothesis':0}},fix(call(f,[var('delta_hole'),*args]))),use(n['indexed_'+op+'_preserves_metadata'],[tree,*args]),lift({'Hypothesis':0},call(f,[var('delta_hole'),*args])))
                allrules.append(law([['bridge_tree',T],*rest],a,z,p,[valid]))
        option=objects[t['get']]['payload']['declaration']['Function']['result']['Data']
        functions['contains']=fun([['bridge_tree',T],['bridge_key',objects[t['get']]['payload']['declaration']['Function']['params'][1][1]]],'Bool',match(call(functions['get'],[tree,key]),[([],{'Bool':False}),(['present_row'],{'Bool':True})]))
        layout['functions']=functions
        for q in layout['queries']:
            a=call(q['projection'],[call(n['sum'],[tree])]);z=sub(q['term'],{q['binding']:decode(tree)})
            p=trans(lift({'Sym':{'Hypothesis':0}},call(q['projection'],[call(n['sum'],[var('delta_hole')])])),{'Call':dict(function=q['projection'],arguments=[use(n['sum_repair_matches_rows'],[tree])])},use(q['product_projection'],[decode(tree)]),{'Sym':use(q['fusion'],[decode(tree)])})
            allrules.append(law([['bridge_tree',T]],a,z,p,[valid]));discovery.append(dict(action=q['name'],table=q['index'],sort=q['sort']))
    if batching:
        from producers.grouped_indexed import build
        for index,layout in enumerate(layouts.values()):
            layout['grouped']=build(layout,objects,add,fun,law,allrules,opaque)
            names.update({'table-'+str(index)+'/grouped/'+k:v for k,v in layout['grouped_proofs'].items()})
    L={'Data':model['state']};fields=objects[model['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields'];physical_fields=[{'Data':layouts[f['Data']]['roles']['tree']} for f in fields]
    physical=add({'Datatype':dict(constructors=[dict(name='IndexedState',fields=physical_fields)])});P={'Data':physical};bindings=['indexed_root_'+str(i) for i in range(len(fields))]
    roots=[var(n) for n in bindings];bound=cons(physical,0,roots)
    decoded_roots=[call(layouts[f['Data']]['roles']['decode'],[v]) for f,v in zip(fields,roots)];logical=cons(model['state'],0,decoded_roots)
    encode=fun([['logical',L]],P,match(var('logical'),[(bindings,cons(physical,0,[call(layouts[f['Data']]['roles']['encode_rows'],[v]) for f,v in zip(fields,roots)]))]))
    decode=fun([['physical',P]],L,match(var('physical'),[(bindings,logical)]))
    repaired_roots=[call(layouts[f['Data']]['roles']['repair'],[v]) for f,v in zip(fields,roots)];repaired=cons(physical,0,repaired_roots)
    repair=fun([['physical',P]],P,match(var('physical'),[(bindings,repaired)]));fresh=lambda p:call(repair,[p])
    roundtrip=law([['logical',L]],call(decode,[call(encode,[var('logical')])]),var('logical'),induction('logical',call(decode,[call(encode,[var('logical')])]),var('logical'),bindings,{'Construct':dict(datatype=model['state'],constructor=0,arguments=[use(layouts[f['Data']]['roles']['encode_preserves_rows'],[v]) for f,v in zip(fields,roots)])}))
    a,z=fresh(call(encode,[var('logical')])),call(encode,[var('logical')]);init_metadata=law([['logical',L]],a,z,induction('logical',a,z,bindings,{'Construct':dict(datatype=physical,constructor=0,arguments=[use(layouts[f['Data']]['roles']['encode_preserves_metadata'],[v]) for f,v in zip(fields,roots)])}))
    allrules.extend([roundtrip,init_metadata])
    from producers.type_transport import Transport
    transport=Transport(objects,add,fun,law,{model['state']:(physical,encode,decode,roundtrip),**{d:(layout['roles']['tree'],layout['roles']['encode_rows'],layout['roles']['decode'],layout['roles']['encode_preserves_rows']) for d,layout in layouts.items()}},allrules)
    left=fun([['physical',P],['logical',L]],L,call(decode,[var('physical')]));right=fun([['physical',P],['logical',L]],L,var('logical'))
    metadata_left=fun([['physical',P],['logical',L]],P,fresh(var('physical')));metadata_right=fun([['physical',P],['logical',L]],P,var('physical'))
    table_ops={t[op]:(t,op) for t in model['tables'] for op in ['get','contains','insert','remove','replace']};actions={}
    for name,action in model['actions'].items():
        source_observation=action['result']['Data'];constructors=objects[source_observation]['payload']['declaration']['Datatype']['constructors']
        observation=add({'Datatype':dict(constructors=[dict(name=c['name'],fields=[P if f==L else f for f in c['fields']]) for c in constructors])});O={'Data':observation}
        state_variables=dict(zip(action['case']['bindings'],fields));rename=dict(zip(action['case']['bindings'],bindings))
        initial_env={n:(s,s) for n,s in action['params'][1:]};initial_env.update({n:(s,transport.sort(s)) for n,s in state_variables.items()})
        def cache_match(pattern,t,hole,found):
            if pattern==var(hole):
                if found and found[0]!=t:return False
                if not found:found.append(t)
                return True
            if type(pattern)!=type(t):return False
            if isinstance(pattern,dict):return pattern.keys()==t.keys() and all(cache_match(pattern[k],t[k],hole,found) for k in pattern)
            if isinstance(pattern,list):return len(pattern)==len(t) and all(cache_match(a,b,hole,found) for a,b in zip(pattern,t))
            return pattern==t
        def translate(t,allow_cache=True,env=None):
            env=initial_env if env is None else env
            if not isinstance(t,dict):raise ValueError('invalid action term')
            if allow_cache:
                for layout in layouts.values():
                    for q in layout['queries']:
                        found=[]
                        if cache_match(q['term'],t,q['binding'],found) and found:
                            root,sort=translate(found[0],False,env)
                            if sort=={'Data':layout['roles']['tree']}:return call(q['projection'],[call(layout['roles']['sum'],[root])]),q['sort']
            if 'Var' in t:
                n=t['Var'];return var(rename.get(n,n)),env[n][1]
            if 'Construct' in t:
                x=t['Construct'];d=x['datatype'];typed=[translate(a,env=env) for a in x['arguments']];args=[a for a,_ in typed]
                if d in layouts:
                    if x['constructor']==1 and typed[2][1]=={'Data':d}:args[2]=transport.to_physical(args[2],{'Data':d})
                    n=layouts[d]['roles'];return (cons(n['tree'],0,[]) if x['constructor']==0 else call(n['prepend'],args)),{'Data':n['tree']}
                target=transport.sort({'Data':d});decl=objects[d]['payload']['declaration']['Datatype']['constructors'][x['constructor']]
                for i,((a,actual),expected) in enumerate(zip(typed,decl['fields'])):
                    expected={'Data':d} if expected=='SelfType' else expected
                    if actual==expected and transport.sort(expected)!=expected:args[i]=transport.to_physical(a,expected)
                return cons(target['Data'],x['constructor'],args),target
            if 'Call' in t:
                x=t['Call'];f=x['function'];args=[translate(a,env=env) for a in x['arguments']]
                if f in table_ops:
                    table,op=table_ops[f];layout=layouts[table['datatype']]
                    if args[0][1]=={'Data':table['datatype']}:args[0]=(transport.to_physical(args[0][0],args[0][1]),transport.sort(args[0][1]))
                    result=call(layout['functions'][op],[a for a,_ in args])
                    if batching and op in ['insert','replace','remove'] and 'Call' in args[0][0]:
                        inner=args[0][0]['Call'];first=next((kind for kind in ['insert','replace','remove'] if inner['function']==layout['functions'][kind]),None)
                        if first:
                            result=call(layout['grouped'][first,op],[*inner['arguments'],*[a for a,_ in args[1:]]])
                            discovery.append(dict(action=name,grouped=[first,op],table=table['datatype']))
                    return result,{'Data':layout['roles']['tree']} if op in ['insert','replace','remove'] else None
                d=objects[f]['payload']['declaration']['Function'];actual=[]
                for (a,sort),(_,expected) in zip(args,d['params']):
                    if sort==transport.sort(expected) and sort!=expected:a=transport.to_logical(a,expected)
                    actual.append(a)
                result=call(f,actual)
                return transport.to_physical(result,d['result']),transport.sort(d['result'])
            if 'If' in t:
                x=t['If'];a,sort=translate(x['on_true'],env=env);b,_=translate(x['on_false'],env=env);return {'If':dict(condition=translate(x['condition'],env=env)[0],on_true=a,on_false=b)},sort
            if 'Binary' in t:
                x=t['Binary'];return {'Binary':dict(op=x['op'],left=translate(x['left'],env=env)[0],right=translate(x['right'],env=env)[0])},transport.infer(t,env)
            if 'Match' in t:
                x=t['Match'];original=transport.infer(x['scrutinee'],env);scrutinee,sort=translate(x['scrutinee'],env=env)
                logical_match=original.get('Data') in layouts if isinstance(original,dict) else False
                if logical_match and sort!=original:scrutinee=transport.to_logical(scrutinee,original)
                branches=[];constructors=objects[original['Data']]['payload']['declaration']['Datatype']['constructors']
                for b,c in zip(x['branches'],constructors):
                    sorts=[original if f=='SelfType' else f for f in c['fields']]
                    local={**env,**{n:(s,s if logical_match or sort==original else transport.sort(s)) for n,s in zip(b['bindings'],sorts)}}
                    branches.append((b['bindings'],translate(b['body'],env=local)[0]))
                return match(scrutinee,branches),transport.sort(transport.infer(t,env))
            return t,transport.infer(t,env)
        normal,_=translate(action['case']['normal'])
        if batching:
            from producers.point_delta import normal as normalize
            operations={layout['functions'][op]:(layout,op) for layout in layouts.values() for op in ['insert','replace','remove']}
            # Expose projections of constructed states before grouping. This is
            # ordinary conversion, including transitions around intermediate reads.
            normal=normalize(normal,objects,opaque=[*opaque,*operations])
            def group(t):
                if isinstance(t,list):return [group(x) for x in t]
                if not isinstance(t,dict):return t
                if 'Call' in t and t['Call']['function'] in operations:
                    t=normalize(t,objects,opaque=[*opaque,*operations])
                t={k:group(v) for k,v in t.items()}
                if 'Call' in t and t['Call']['function'] in operations:
                    x=t['Call'];layout,second=operations[x['function']];inner=x['arguments'][0].get('Call')
                    if inner and inner['function'] in operations:
                        other,first=operations[inner['function']]
                        if other is layout:
                            discovery.append(dict(action=name,grouped=[first,second],table=layout['table']['datatype']))
                            return call(layout['grouped'][first,second],[*inner['arguments'],*x['arguments'][1:]])
                return t
            normal=group(normal)
        rest=action['params'][1:];args=[var(n) for n,_ in rest]
        execute=fun([['physical',P],*rest],O,match(var('physical'),[(bindings,normal)]))
        onames=['indexed_reply','indexed_commit','indexed_version','indexed_post','indexed_events'];hnames=['indexed_error','indexed_version','indexed_post']
        observe=fun([['observation',O]],action['result'],match(var('observation'),[(onames,cons(source_observation,0,[var(onames[0]),var(onames[1]),var(onames[2]),call(decode,[var(onames[3])]),var(onames[4])])),(hnames,cons(source_observation,1,[var(hnames[0]),var(hnames[1]),call(decode,[var(hnames[2])])]))]))
        nextf=fun([['observation',O]],P,match(var('observation'),[(onames,var(onames[3])),(hnames,var(hnames[2]))]))
        post=fun([['source',action['result']]],L,match(var('source'),[(onames,var(onames[3])),(hnames,var(hnames[2]))]))
        obs=lambda p:call(observe,[call(execute,[p,*args])]);a,z=obs(fresh(var('physical'))),call(action['function'],[call(decode,[var('physical')]),*args])
        case_params=[[n,ty] for n,ty in zip(bindings,physical_fields)]+rest;tactic=Tactic(objects,allrules,opaque=opaque,prove_conditions=True,add=add,params=case_params)
        p=tactic.prove(sub(a,{'physical':bound}),sub(z,{'physical':bound}));p=factor(p,case_params,[],add,objects)
        exact=law([['physical',P],*rest],a,z,induction('physical',a,z,bindings,p))
        observation_proof=trans(lift({'Sym':{'Hypothesis':1}},obs(var('delta_hole'))),use(exact,[var('physical'),*args]),lift({'Hypothesis':0},call(action['function'],[var('delta_hole'),*args])))
        a=call(decode,[call(nextf,[var('observation')])]);z=call(post,[call(observe,[var('observation')])])
        commuting=law([['observation',O]],a,z,{'Induction':dict(variable='observation',**{'from':a,'to':z},cases=[dict(bindings=ns,proof=convert(sub(a,{'observation':cons(observation,i,[var(n) for n in ns])}),sub(z,{'observation':cons(observation,i,[var(n) for n in ns])}))) for i,ns in enumerate([onames,hnames])])})
        executed=call(execute,[var('physical'),*args]);preservation=trans(use(commuting,[executed]),lift(observation_proof,call(post,[var('delta_hole')])))
        n=lambda p:call(nextf,[call(execute,[p,*args])]);a,z=fresh(n(fresh(var('physical')))),n(fresh(var('physical')))
        proof=tactic.prove(sub(a,{'physical':bound}),sub(z,{'physical':bound}));proof=factor(proof,case_params,[],add,objects)
        maintains=law([['physical',P],*rest],a,z,induction('physical',a,z,bindings,proof))
        metadata=trans(lift({'Sym':{'Hypothesis':1}},fresh(n(var('delta_hole')))),use(maintains,[var('physical'),*args]),lift({'Hypothesis':1},n(var('delta_hole'))))
        actions[name]=dict(execute=execute,result=O,next=nextf,observe=observe,preservation=[preservation,metadata],observation=observation_proof)
    plan=dict(source_objects=sorted(model['objects']),logical_state=L,physical_state=P,encode=encode,decode=decode,relations=[dict(left=left,right=right),dict(left=metadata_left,right=metadata_right)],initialisation=[use(roundtrip,[var('logical')]),use(init_metadata,[var('logical')])],snapshot={'Hypothesis':0},actions=actions)
    e=entry('representation',REP,plan,refs(plan),parameters={'logical':L},result=P,effects=['source-transitions']);e['interface']['operations']=sorted(actions);rid=identity(e);objects[rid]=e;names['representation']=rid
    store=Store.publish(directory,objects.values(),names,leaf_size=2);request=dict(schema=1,semantics=REP,input_core_sha256=model['source'],knowledge=store.bundle([rid]),representation=rid)
    return dict(request=request,discovery=discovery,layouts=layouts)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('model',type=Path);p.add_argument('-o',type=Path,required=True)
    p.add_argument('--no-batching',action='store_true')
    p.add_argument('--publish-root',type=Path);p.add_argument('--source',type=Path)
    p.add_argument('--compiler',type=Path);p.add_argument('--report',type=Path)
    a=p.parse_args()
    if a.publish_root and not all([a.source,a.compiler,a.report]):p.error('publication requires source, compiler and report')
    result=generate(read(a.model),a.o.parent/'database',batching=not a.no_batching)
    a.o.parent.mkdir(exist_ok=True,parents=True)
    a.o.write_bytes(canonical(result['request'])+b'\n')
    a.o.with_suffix('.discovery.json').write_text(json.dumps(result['discovery'],indent=2)+'\n')
    if a.publish_root:
        from producers.indexed_aggregate import publish_checked
        print(json.dumps(publish_checked(a.o.parent,a.publish_root,a.compiler,a.source,a.report,candidate_root=a.o.parent/'database',publish_implementations=True)))
if __name__=='__main__':main()
