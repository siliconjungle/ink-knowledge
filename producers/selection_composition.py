"""Untrusted whole-function equality construction from ordinary selected steps.

The result uses existing Use/Forall/Cases/Congruence/Trans proofs. It must replay
as a normal law and selection; source paths or prior selection never grant proof
authority. Unsupported ambient facts can make a proposed composition fail replay.
"""
import copy
from ink_knowledge import identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_planner.semantic_search import children,replace,substitute
from producers.beta_specialization15 import instantiate_bound,free_parameters
from producers.contract_proofs import proof_semantics
from producers.definition_context28 import bind
from producers.semantic_laws import law,var


def compose(packet,subject,core,store,directory):
    if packet['input_core_sha256']!=subject['input_core_sha256']:
        raise ValueError('whole-function composition source mismatch')
    applications=packet['applications']
    if not 1<=len(applications)<=128:raise ValueError('whole-function composition application budget')
    functions={f['name']:f for f in core['program']['functions']}
    affected={a['function']for a in applications}
    bodies={name:copy.deepcopy(subject['functions'][name])for name in affected if name in subject['functions']}
    initial=copy.deepcopy(bodies)
    objects=dict(packet['knowledge']['objects']);chains={};occupied=set();work=[0]
    def strings(v,depth=0):
        work[0]+=1
        if work[0]>200000 or depth>256:raise ValueError('whole-function composition work budget')
        if isinstance(v,str):occupied.add(v)
        elif isinstance(v,dict):
            for k,x in v.items():occupied.add(k);strings(x,depth+1)
        elif isinstance(v,list):
            for x in v:strings(x,depth+1)
    strings([bodies,applications])
    def fresh():
        name='composed_argument'
        while name in occupied:name+='_' 
        if len(name)>128:raise ValueError('whole-function composition binder budget')
        occupied.add(name);return name
    def opened(proof,argument,depth):
        work[0]+=1
        if work[0]>200000:raise ValueError('whole-function composition work budget')
        if isinstance(proof,dict):
            if set(proof)=={'sort','node'}:return instantiate_bound(proof,argument,depth)
            return {k:opened(v,argument,depth)for k,v in proof.items()}
        if isinstance(proof,list):return [opened(v,argument,depth)for v in proof]
        return proof
    def trans(middle,left,right):return {'Trans':dict(middle=middle,left=left,right=right)}
    def lift(before,after,path,use,depth):
        work[0]+=1
        if work[0]>200000 or len(path)>128:raise ValueError('whole-function composition proof budget')
        if not path:return use
        index=path[0];node=before['node'];a=children(before);b=children(after)
        if isinstance(node,dict)and 'Lambda'in node:
            if index!=0:raise ValueError('whole-function composition lambda path')
            name=fresh();argument=var(before['sort']['Arrow'][0],name)
            return {'Forall':dict(parameter=name,body=lift(
                instantiate_bound(a[0],argument),instantiate_bound(b[0],argument),path[1:],
                opened(use,argument,depth-1),depth-1))}
        operator=node.get('Op')if isinstance(node,dict)else None
        # Branch facts become explicit proof scopes, including lazy Boolean RHS.
        branch=None
        if operator and operator[0]=='call:choose'and index in (1,2):branch=index==1
        elif operator and operator[0]in ('binary:&&','binary:||')and index==1:branch=operator[0]=='binary:&&'
        if branch is not None:
            step=lift(a[index],b[index],path[1:],use,depth)
            selected=trans(a[index],'Normalize',trans(b[index],step,'Normalize'))
            return {'Cases':dict(condition=a[0],on_true=selected if branch else 'Normalize',
                on_false='Normalize'if branch else selected)}
        return {'Congruence':[lift(x,b[i],path[1:],use,depth)if i==index else 'Normalize'for i,x in enumerate(a)]}
    for app in applications:
        name=app['function'];path=app['path']
        if name not in functions or name not in bodies:raise ValueError('whole-function composition requires a pure semantic root')
        if any(type(i)is not int or i<0 for i in path):raise ValueError('whole-function composition path')
        before=bodies[name];target=before;depth=0
        for index in path:
            depth+=int(isinstance(target['node'],dict)and 'Lambda'in target['node'])
            parts=children(target)
            if index>=len(parts):raise ValueError('whole-function composition path')
            target=parts[index]
        entry=objects[app['law']];payload=entry['payload']
        if payload.get('types')or payload.get('assumptions'):raise ValueError('instantiate general laws before composition')
        if substitute(payload['from'],app['arguments'])!=target:raise ValueError('whole-function composition endpoint mismatch')
        after=replace(before,path,substitute(payload['to'],app['arguments']))
        use={'Use':dict(law=app['law'],arguments=copy.deepcopy(app['arguments']),premises=copy.deepcopy(app['premises']))}
        proof=lift(before,after,path,use,depth)
        chains.setdefault(name,[]).append((before,after,proof));bodies[name]=after
    def balanced(steps,start,end):
        if end-start==1:return steps[start][2]
        middle=(start+end)//2
        return trans(steps[middle-1][1],balanced(steps,start,middle),balanced(steps,middle,end))
    roots=set(packet['knowledge']['roots']);composed=[]
    for name,steps in sorted(chains.items()):
        params=free_parameters(initial[name])
        for n,s in free_parameters(bodies[name]).items():
            if n in params and params[n]!=s:raise ValueError('whole-function composition parameter sort')
            params[n]=s
        allowed={n for n,_ in functions[name]['params']}
        if set(params)-allowed:raise ValueError('whole-function composition introduced a free parameter')
        # Premise certificates may mention a declared parameter erased by the
        # resulting expression. Preserve its sort without leaking local binders.
        def parameters(v):
            if isinstance(v,dict):
                if set(v)=={'sort','node'}:
                    for n,s in free_parameters(v).items():
                        if n in allowed:
                            if n in params and params[n]!=s:raise ValueError('whole-function composition parameter sort')
                            params[n]=s
                else:
                    for x in v.values():parameters(x)
            elif isinstance(v,list):
                for x in v:parameters(x)
        for app in applications:
            if app['function']==name:parameters([app['arguments'],app['premises']])
        proof=balanced(steps,0,len(steps))
        authored=law(params,initial[name],bodies[name],proof,dependencies=sorted(roots))
        authored['semantics']=proof_semantics(proof);authored=bind(authored,core,subject)
        obj=semantic_entry(authored);ident=identity(obj);objects[ident]=obj
        composed.append(dict(function=name,path=[],law=ident,arguments={n:var(s,n)for n,s in params.items()},premises=[]))
    view=ProposalViews(store,objects,directory)
    return dict(packet,applications=composed,knowledge=view.bundle(sorted(roots|{a['law']for a in composed})))
