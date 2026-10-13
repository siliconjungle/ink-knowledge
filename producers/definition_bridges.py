"""Ordinary induction lemmas for alpha-equivalent generated definitions.

Content identities deliberately include lexical names. These untrusted lemmas
allow action proofs to survive unrelated changes in fresh-name allocation.
Every bridge is a theorem in the same local first-order kernel.
"""
import hashlib,json,os,sys
from producers.action_replacement import var,call,cons,convert,trans,alpha_normal
from producers.point_delta import normal,sub,replace,free_variables
from producers.state_laws import derive
from producers.representations import refs
from ink_knowledge import identity
from ink_knowledge.store import entry

def bridges(before,after,objects):
    cache={}
    def shape(i):
        if i in cache:return cache[i]
        d=objects[i]['payload']['declaration'].get('Function')
        if not d:return i
        body=alpha_normal(d['body'],env={n:'parameter_'+str(j)for j,(n,_)in enumerate(d['params'])})
        def links(t):
            if isinstance(t,list):return [links(x)for x in t]
            if not isinstance(t,dict):return t
            if 'Call'in t:return {'Call':dict(function=shape(t['Call']['function']),arguments=links(t['Call']['arguments']))}
            return {k:links(x)for k,x in t.items()}
        result=hashlib.sha256(json.dumps([list(s for _,s in d['params']),d['result'],d['recursive'],links(body)],sort_keys=True).encode()).hexdigest();cache[i]=result;return result
    groups={}
    for i,o in {**before,**after}.items():
        if 'Function'in o['payload'].get('declaration',{}):groups.setdefault(shape(i),[]).append(i)
    pairs={i:min(ids)for ids in groups.values()for i in ids if i!=min(ids)}
    lemmas={};active=set()
    def add(d):
        obj=entry('theorem','first-order-inductive-equality-v1',dict(declaration=d),refs(d),parameters=dict(d['Theorem']['params']),conditions=[]);i=identity(obj);objects[i]=obj;return i
    def calls(t):
        if isinstance(t,list):
            for x in t:yield from calls(x)
        elif isinstance(t,dict):
            if 'Call'in t:yield t
            for x in t.values():yield from calls(x)
    def prove_pair(i):
        if i in lemmas:return lemmas[i]
        if i in active:raise ValueError('definition bridge cycle')
        active.add(i);z=pairs[i];f=objects[i]['payload']['declaration']['Function']
        for node in calls([f['body'],objects[z]['payload']['declaration']['Function']['body']]):
            target=node['Call']['function']
            if target in pairs:prove_pair(target)
        params=[['bridge_arg_'+str(j),s]for j,(_,s)in enumerate(f['params'])];args=[var(n)for n,_ in params]
        a,b=call(i,args),call(z,args)
        opaque=tuple(set(pairs)|set(pairs.values()))
        def proof(x,y,ps,hyp=(),depth=0):
            if depth>12:raise ValueError('definition bridge depth')
            # Unfold this pair once; recursive tail calls stay opaque because
            # their recursive argument is not a constructor.
            n=lambda t:normal(t,objects,opaque=tuple(k for k in opaque if k not in (i,z)))
            aa,bb=n(x),n(y);rules=[]
            for node in calls([aa,bb]):
                q=node['Call'];target=q['function']
                if target in lemmas:
                    rules.append((node,call(pairs[target],q['arguments']),{'Use':dict(theorem=lemmas[target],arguments=q['arguments'],premises=[])}))
            # Cases expose any record/list parameter still matched in the body.
            def matched(t):
                if isinstance(t,dict):
                    if 'Match'in t and 'Var'in t['Match']['scrutinee']:yield t['Match']['scrutinee']['Var']
                    for v in t.values():yield from matched(v)
                elif isinstance(t,list):
                    for v in t:yield from matched(v)
            names=set(matched(aa))|set(matched(bb))
            candidate=next(((n,s)for n,s in ps if n in names and isinstance(s,dict)and'Data'in s),None)
            if candidate:
                name,sort=candidate;dt=sort['Data'];cases=[]
                for tag,c in enumerate(objects[dt]['payload']['declaration']['Datatype']['constructors']):
                    bindings=['bridge_case_'+str(depth)+'_'+str(tag)+'_'+str(j)for j in range(len(c['fields']))];node=cons(dt,tag,[var(n)for n in bindings]);mapping={name:node}
                    fields=[{'Data':dt}if s=='SelfType'else s for s in c['fields']]
                    cases.append(dict(bindings=bindings,proof=proof(sub(x,mapping),sub(y,mapping),[(n,s)for n,s in ps if n!=name]+list(zip(bindings,fields)),tuple((sub(a,mapping),sub(b,mapping))for a,b in hyp),depth+1)))
                return {'Cases':dict(variable=name,**{'from':x,'to':y},cases=cases)}
            return trans(convert(x,aa),derive(aa,bb,objects,hyp,rules=rules,opaque=opaque),convert(bb,y))
        if f['recursive']is None:p=proof(a,b,params)
        else:
            at=f['recursive'];name,sort=params[at];dt=sort['Data'];cases=[]
            for tag,c in enumerate(objects[dt]['payload']['declaration']['Datatype']['constructors']):
                bindings=['bridge_root_'+str(tag)+'_'+str(j)for j in range(len(c['fields']))];node=cons(dt,tag,[var(n)for n in bindings]);mapping={name:node}
                fields=[{'Data':dt}if s=='SelfType'else s for s in c['fields']];hyp=[]
                for n,s in zip(bindings,c['fields']):
                    if s=='SelfType':
                        tail=list(args);tail[at]=var(n);hyp.append((call(i,tail),call(z,tail)))
                cases.append(dict(bindings=bindings,proof=proof(sub(a,mapping),sub(b,mapping),[(n,s)for n,s in params if n!=name]+list(zip(bindings,fields)),tuple(hyp))))
            p={'Induction':dict(variable=name,**{'from':a,'to':b},cases=cases)}
        lemma=add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':b},proof=p)});lemmas[i]=lemma;active.remove(i);return lemma
    # Author only bridges that can be discharged by this bounded tactic.
    for i in pairs:
        try:prove_pair(i)
        except(ValueError,KeyError)as e:
            if os.environ.get('INK_BRIDGE_DEBUG'):print('bridge decline',i[:10],str(e)[:220],file=sys.stderr)
            active.clear()
    if os.environ.get('INK_BRIDGE_DEBUG'):print('bridge counts',len(pairs),len(lemmas),file=sys.stderr)
    def rewrite(t):
        current=t;steps=[]
        for _ in range(64):
            found=next((n for n in calls(current)if n['Call']['function']in lemmas and free_variables(n)<=free_variables(current)),None)
            if not found:break
            q=found['Call'];new=call(pairs[q['function']],q['arguments']);p={'Use':dict(theorem=lemmas[q['function']],arguments=q['arguments'],premises=[])}
            steps.append({'Substitute':dict(variable='definition_hole',context=replace(current,found,var('definition_hole')),equality=p)});current=replace(current,found,new)
        return current,steps
    return rewrite,set(lemmas.values())
