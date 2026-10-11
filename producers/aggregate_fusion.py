"""Bind universal aggregate fusion to complete unchanged source queries.

Ordinary source-state induction and congruence lift the per-query fold law;
representation admission rechecks each complete observation and future state.
"""
import copy
from action_replacement import var,call,cons,convert,trans
from point_delta import sub,match
from representations import refs,MATH
from ink_knowledge import identity
from ink_knowledge.store import entry


def replacement(model,queries):
    objects=dict(model['objects']);selected=copy.deepcopy(model)
    carriers=[i for i,o in objects.items()if 'Datatype'in o['payload'].get('declaration',{})]
    def add(decl,extra=()):
        payload={'declaration':decl};body=next(iter(decl.values()))
        obj=entry('theorem'if'Theorem'in decl else'definition',MATH,payload,refs(payload)|set(extra)|set(carriers),parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]))
        i=identity(obj);objects[i]=obj;return i
    proofs={name:{'Refl':call(a['function'],[var(n)for n,_ in a['params']])}for name,a in model['actions'].items()}
    from aggregate_delta import setup
    for name in queries:
        action=model['actions'][name]
        if len(action['params'])!=2:raise ValueError('aggregate fusion currently needs parameterless queries')
        delta=setup(model,action,add,objects,specialized=True)
        normal=copy.deepcopy(action['case']['normal']);normal['Construct']['arguments'][0]=delta['fused']
        declaration={'Function':dict(params=action['params'],result=action['result'],body=match(var(action['params'][0][0]),[(action['case']['bindings'],normal)]),recursive=None)}
        function=add(declaration);selected['actions'][name]['function']=function;selected['actions'][name]['case']['normal']=normal
        selected['actions'][name]['case']['call']=call(function,[var(n)for n,_ in action['params']])
        bound=cons(model['state'],0,[var(n)for n in action['case']['bindings']])
        args=[var(n)for n,_ in action['params'][1:]]
        a,z=call(action['function'],[bound,*args]),call(function,[bound,*args])
        old=action['case']['normal'];new=normal
        value_proof=delta['fusion'](var(action['case']['bindings'][0]))
        bodyproof={'Construct':dict(datatype=old['Construct']['datatype'],constructor=old['Construct']['constructor'],arguments=[value_proof,*[{'Refl':t}for t in old['Construct']['arguments'][1:]]])}
        start=call(action['function'],[var(n)for n,_ in action['params']]);end=call(function,[var(n)for n,_ in action['params']])
        proofs[name]={'Induction':dict(variable=action['params'][0][0],**{'from':start,'to':end},cases=[dict(bindings=action['case']['bindings'],proof=trans(convert(a,old),bodyproof,convert(new,z)))])}
    selected['objects']=objects
    return dict(input_core_sha256=model['source'],knowledge=dict(objects=objects),selected_model=selected,action_replacement=dict(proofs=proofs))
