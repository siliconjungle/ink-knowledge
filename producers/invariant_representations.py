"""Propose observation simplifications from exact source-state invariants.

Invariants and representations are data. This producer proposes smaller ordinary
first-order bodies and proves complete observations/future-state preservation.
It never adds an ambient assumption to a nested source call.
"""
import argparse,copy,json,subprocess
from pathlib import Path
from ink_knowledge import Store,entry,identity
from producers.representations import generate as baseline,refs,match,subst,unchanged_query
from producers.action_replacement import var,call,cons,trans
from producers.contract_proofs import state_proof
from producers.equational import Tactic
from producers.point_delta import sub

SEMANTICS='ink-source-representation-v2'
MATH='first-order-inductive-equality-v1'

def size(value):
    if isinstance(value,dict):return 1+sum(size(v)for v in value.values())
    if isinstance(value,list):return sum(size(v)for v in value)
    return 1

def simplify(value,facts):
    def visit(term,depth=0):
        if depth>64:raise ValueError('invariant simplification depth')
        if isinstance(term,list):term=[visit(x,depth+1)for x in term]
        elif isinstance(term,dict):term={k:visit(v,depth+1)for k,v in term.items()}
        for a,z in facts:
            if term==a and size(z)<size(a):return copy.deepcopy(z)
        return term
    for _ in range(16):
        updated=visit(value)
        if updated==value:return value
        value=updated
    raise ValueError('invariant simplification budget')

def generate(model,directory,compiler,max_queries=16):
    if not model.get('source_domain'):return dict(requests=[],declined=['no checked source invariants'])
    if not 1<=max_queries<=64:raise ValueError('invariant query budget')
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    base=baseline(model,directory/'baseline',source_domain=True)['requests'][0]
    objects=copy.deepcopy(base['knowledge']['objects']);plan=copy.deepcopy(objects[base['representation']]['payload'])
    tactic=Tactic(objects);physical=plan['physical_state'];logical=plan['logical_state'];changed=[];declined=[]
    physical_decl=objects[physical['Data']]['payload']['declaration']['Datatype']
    carriers={i for i,o in objects.items()if 'Datatype'in o.get('payload',{}).get('declaration',{})}
    def add(declaration):
        body=next(iter(declaration.values()));payload=dict(declaration=declaration)
        # Match scrutinee/field sorts may occur only in a called function's
        # signature. Import those source carriers explicitly, as core does.
        obj=entry('definition',MATH,payload,refs(payload)|carriers,parameters=dict(body.get('params',[])),result=body.get('result'))
        ident=identity(obj);objects[ident]=obj;return ident
    for name,source in sorted(model['actions'].items()):
        if len(changed)>=max_queries:break
        if not unchanged_query(model,source):continue
        original=plan['actions'][name];signature=objects[original['execute']]['payload']['declaration']['Function'];params=signature['params'];args=[var(n)for n,_ in params];branches=[];improved=False
        for index,constructor in enumerate(physical_decl['constructors']):
            names=[f'__invariant_field_{index}_{i}'for i in range(len(constructor['fields']))]
            if any(n in dict(params)for n in names):raise ValueError('invariant field capture')
            bound=cons(physical['Data'],index,[var(n)for n in names]);decoded=tactic.norm(call(plan['decode'],[bound]))
            facts=[(tactic.norm(sub(e['from'],{'logical':decoded})),tactic.norm(sub(e['to'],{'logical':decoded})))for e in model['source_domain']]
            before=tactic.norm(call(original['execute'],[bound,*args[1:]]));after=simplify(before,facts)
            improved|=size(after)<size(before);branches.append((names,after))
        if not improved:continue
        execute=add({'Function':dict(params=params,result=signature['result'],body=match(var(params[0][0]),branches),recursive=None)})
        conditions=[dict(**{'from':call(r['left'],[var('physical'),var('logical')]),'to':call(r['right'],[var('physical'),var('logical')])})for r in plan['relations']]
        conditions.extend(model['source_domain']);env={'physical':physical,'logical':logical,**dict(params[1:])}
        execution_args=[var('physical'),*args[1:]]
        new=call(execute,execution_args);old=call(original['execute'],execution_args)
        try:
            proof=state_proof(objects,new,old,env,[(e['from'],e['to'],i)for i,e in enumerate(conditions)])
        except ValueError as error:declined.append(dict(action=name,reason=str(error)));continue
        current=copy.deepcopy(original);current['execute']=execute
        current['observation']=trans(subst(proof,call(current['observe'],[var('replacement')])),original['observation'])
        # All logical post-state and event obligations retain their exact source.
        current['preservation']=[trans(subst(proof,call(r['left'],[call(current['next'],[var('replacement')]),
            {'Match':dict(scrutinee=call(source['function'],[var('logical'),*args[1:]]),branches=[
                dict(bindings=['__r','__c','__v','__s','__e'],body=var('__s')),
                dict(bindings=['__h','__v','__s'],body=var('__s'))])}])),old_proof)
            for r,old_proof in zip(plan['relations'],original['preservation'])]
        plan['actions'][name]=current;changed.append(name)
    if not changed:return dict(requests=[],declined=declined)
    obj=entry('representation',SEMANTICS,plan,refs(plan),parameters={'logical':logical},result=physical,effects=['source-transitions'],conditions=[{'source_domain':'checked-source-invariants'}]);obj['interface']['operations']=sorted(plan['actions']);ident=identity(obj);objects[ident]=obj
    store=Store.publish(directory/'store',objects.values(),{'invariants/observations':ident});request=dict(schema=1,semantics=SEMANTICS,input_core_sha256=model['source'],knowledge=store.bundle([ident]),representation=ident)
    path=directory/'request.json';path.write_text(json.dumps(request))
    trial=subprocess.run([str(compiler),'check-representation','--core',str(directory/'source.core.json'),str(path)],capture_output=True,text=True)if (directory/'source.core.json').exists()else None
    if trial is not None and trial.returncode:raise ValueError(trial.stderr)
    return dict(requests=[request],changed=changed,declined=declined)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('model',type=Path);p.add_argument('--compiler',required=True);p.add_argument('-o','--output',type=Path,required=True);p.add_argument('--max-queries',type=int,default=16);a=p.parse_args()
    result=generate(json.loads(a.model.read_text()),a.output.parent/'invariant-database',a.compiler,a.max_queries);a.output.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
