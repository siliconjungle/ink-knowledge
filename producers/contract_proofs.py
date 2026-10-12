"""Untrusted source-contract proof authoring and canonical database publication.

Every proposed proof is replayed against the compiler's source-derived obligation.
The catalogue records correctness; measurements separately establish profitability.
"""
import argparse, json, subprocess
from pathlib import Path
from ink_knowledge.store import Store, entry, semantic_entry, identity
from producers.equational import Tactic
from producers.action_replacement import var, cons, convert
from producers.point_delta import sub, normal

MATH='first-order-inductive-equality-v1'

def references(value):
    if isinstance(value,list):return set().union(*(references(x) for x in value))
    if not isinstance(value,dict):return set()
    found={v for k,v in value.items() if k in ('Data','datatype','function','theorem') and isinstance(v,str) and len(v)==64}
    return found|set().union(*(references(x) for x in value.values()))

def context_for(context,goal):
    """Keep only definitions and value types actually mentioned by this law."""
    functions=set();types=set()
    def scan(t):
        if isinstance(t,dict):
            op=t.get('Op')
            if isinstance(op,list) and op and isinstance(op[0],str) and op[0].startswith('call:') and op[0][5:] in context['definitions']:functions.add(op[0][5:])
            if isinstance(t.get('Named'),str):types.add(t['Named'])
            for v in t.values():scan(v)
        elif isinstance(t,list):
            for v in t:scan(v)
    scan(goal);seen=set()
    while functions-seen:
        name=next(iter(functions-seen));seen.add(name);definition=context['definitions'][name]
        scan(definition);functions.update(definition['definition']['callees'])
    seen_types=set()
    while types-seen_types:
        name=next(iter(types-seen_types));seen_types.add(name);scan(context['records'].get(name,[]))
    return dict(schema=1,definitions={n:context['definitions'][n] for n in sorted(functions)},records={n:t for n,t in context['records'].items() if n in types},enums={n:t for n,t in context['enums'].items() if n in types},**({'ids':[n for n in context.get('ids',[]) if n in types]} if any(n in types for n in context.get('ids',[])) else {}))

def state_proof(objects,a,z,params,hyp=(),depth=0,serial=None):
    """Bounded ordinary constructor induction and Boolean case proof search."""
    if depth>18:raise ValueError('contract proof search depth')
    serial=serial if serial is not None else [0,0]
    serial[1]+=1
    if serial[1]>100000:raise ValueError("contract proof search node budget")
    tactic=Tactic(objects)
    from producers.action_replacement import trans
    from producers.point_delta import lift
    from producers.equational import alpha
    def replace(t,old,new):
        if alpha(t)==alpha(old):return new
        if isinstance(t,dict):return {k:replace(v,old,new) for k,v in t.items()}
        if isinstance(t,list):return [replace(v,old,new) for v in t]
        return t
    facts=[(tactic.norm(x),tactic.norm(y),trans(convert(tactic.norm(x),x),{'Hypothesis':i},convert(y,tactic.norm(y)))) for x,y,i in hyp]
    def contradiction():
        for x,y,proof in facts:
            if 'Bool' in x and 'Bool' in y and x!=y:
                context={'If':dict(condition=var('delta_hole'),on_true=a if x['Bool'] else z,on_false=z if x['Bool'] else a)}
                return trans(convert(a,sub(context,{'delta_hole':x})),lift(proof,context),convert(sub(context,{'delta_hole':y}),z))
        return None
    impossible=contradiction()
    if impossible:return impossible
    def simplify(value,others):
        current=tactic.norm(value);proof=convert(value,current)
        for _ in range(16):
            changed=False
            for x,y,p in others:
                if x==y:continue
                following=replace(current,x,y)
                if following!=current:
                    proof=trans(proof,lift(p,replace(current,x,var('delta_hole'))),convert(following,tactic.norm(following)))
                    current=tactic.norm(following);changed=True;break
            if not changed:return current,proof
        raise ValueError('contract fact rewrite budget')
    for _ in range(4):
        updated=False
        for i,(x,y,p) in enumerate(facts):
            others=facts[:i]+facts[i+1:];xx,px=simplify(x,others);yy,py=simplify(y,others)
            if (xx,yy)!=(x,y):facts[i]=(xx,yy,trans({'Sym':px},p,py));updated=True
            impossible=contradiction()
            if impossible:return impossible
        if not updated:break
    na,pa=simplify(a,facts);nz,pz=simplify(z,facts)
    def nodes(t):
        if isinstance(t,dict):
            yield t
            if 'Match' in t:yield from nodes(t['Match']['scrutinee']);return
            for x in t.values():yield from nodes(x)
        elif isinstance(t,list):
            for x in t:yield from nodes(x)
    if na==nz or ('Binary' in na and na['Binary']['op']=='==' and na['Binary']['left']==na['Binary']['right'] and nz=={'Bool':True}):
        return trans(pa,convert(na,nz),{'Sym':pz})
    from producers.point_delta import free_variables
    for t in nodes([na,nz]):
        if 'If' in t and not any(n in free_variables(t['If']['condition']) and isinstance(sort,dict) and 'Data' in sort and all(n not in free_variables(x)|free_variables(y) for x,y,_ in hyp) for n,sort in params.items()):
            condition=t['If']['condition'];cases={}
            for field,flag in [('on_false',False),('on_true',True)]:
                cases[field]=state_proof(objects,a,z,params,[*hyp,(condition,{'Bool':flag},len(hyp))],depth+1,serial)
            return {'BoolSplit':dict(condition=condition,**{'from':a,'to':z},**cases)}
    from producers.point_delta import free_variables
    # Eliminate an observed constructor shared with a premise without inventing
    # an induction hypothesis for that premise.
    def all_nodes(t):
        if isinstance(t,dict):
            yield t
            for x in t.values():yield from all_nodes(x)
        elif isinstance(t,list):
            for x in t:yield from all_nodes(x)
    premise_nodes=list(all_nodes([x for x,y,p in facts]))
    for node in nodes([na,nz]):
        if 'Match' not in node:continue
        scrutinee=node['Match']['scrutinee']
        if 'Call' not in scrutinee or not any(alpha(scrutinee)==alpha(x) for x in premise_nodes) or not free_variables(scrutinee)<=params.keys():continue
        sort=objects[scrutinee['Call']['function']]['payload']['declaration']['Function']['result']
        if not isinstance(sort,dict) or 'Data' not in sort:continue
        datatype=sort['Data'];cases=[]
        for i,c in enumerate(objects[datatype]['payload']['declaration']['Datatype']['constructors']):
            serial[0]+=1;names=[f'contract_observed_{serial[0]}_{j}' for j in range(len(c['fields']))]
            fields=[sort if t=='SelfType' else t for t in c['fields']];local={**params,**dict(zip(names,fields))}
            value=cons(datatype,i,[var(n) for n in names])
            proof=state_proof(objects,a,z,local,[*hyp,(scrutinee,value,len(hyp))],depth+1,serial)
            cases.append(dict(bindings=names,proof=proof))
        return {'Cases':dict(scrutinee=scrutinee,**{'from':a,'to':z},cases=cases)}
    free=free_variables(na)|free_variables(nz)
    for variable,sort in params.items():
        if variable not in free or not isinstance(sort,dict) or 'Data' not in sort:continue
        datatype=sort['Data'];d=objects[datatype]['payload']['declaration']
        if 'Datatype' not in d:continue
        induct=all(variable not in free_variables(x)|free_variables(y) for x,y,_ in hyp)
        cases=[]
        for i,c in enumerate(d['Datatype']['constructors']):
            serial[0]+=1;names=[f'contract_case_{serial[0]}_{j}' for j in range(len(c['fields']))]
            value=cons(datatype,i,[var(n) for n in names]);binding={variable:value};local={n:t for n,t in params.items() if n!=variable}
            fields=[sort if t=='SelfType' else t for t in c['fields']];local.update(zip(names,fields))
            premises=list(hyp) if induct else [(sub(x,binding),sub(y,binding),j) for x,y,j in hyp]
            if induct:
                for name,field in zip(names,fields):
                    if field==sort:premises.append((sub(a,{variable:var(name)}),sub(z,{variable:var(name)}),len(premises)))
            proof=state_proof(objects,sub(a,binding),sub(z,binding),local,premises,depth+1,serial)
            cases.append(dict(bindings=names,proof=proof))
        return {('Induction' if induct else 'Cases'):dict(variable=variable,**{'from':a,'to':z},cases=cases)}
    raise ValueError('unclosed contract state goal '+str((na,nz))[:600])

def author(compiler,source,directory,bodies=None,source_evidence=None):
    compiler=str(Path(compiler).resolve());source=str(Path(source).resolve())
    directory=Path(directory).resolve();directory.mkdir(parents=True,exist_ok=True)
    options=["--core"] if Path(source).suffix==".json" else []
    if source_evidence:options += ['--contract-proofs',str(Path(source_evidence).resolve())]
    if bodies:options += ['--refinement-bodies',str(Path(bodies).resolve())]
    export=directory/'obligations.json'
    subprocess.run([compiler,'emit-contract-obligations',source,'-o',str(export),*options],check=True,capture_output=True,text=True)
    goals=json.loads(export.read_text());pure_objects={};state_objects=dict((goals['state'] or {}).get('objects',{}));pure_roots=[];state_roots=[]
    proofs={};state_proofs={};names={}
    def check(g,proof,bundle=None):
        path=directory/'trial.json';path.write_text(json.dumps(dict(proof=proof,knowledge=bundle)))
        trial=subprocess.run([compiler,'check-contract-proof',source,g['name'],str(path),*options],capture_output=True,text=True)
        if trial.returncode:(directory/"last-check-error.txt").write_text(trial.stderr)
        return trial.returncode==0
    for g in goals['pure']:
        candidates=['Normalize',*[{'Hypothesis':i} for i in range(len(g['conditions']))]]
        for n,t in g['params'].items():
            if isinstance(t,dict) and isinstance(t.get('Value'),dict) and 'List' in t['Value']:
                candidates.append({'Induction':dict(variable=n,names=['contract_head','contract_tail'],base='Normalize',step='Normalize')})
        proof=next((p for p in candidates if check(g,p)),None)
        if proof is None:raise ValueError('no checked proof for '+g['name'])
        law=dict(schema=1,semantics='ink-conditional-laws-v1',params=g['params'],conditions=g['conditions'],**g['goal'],proof=proof,dependencies=[],definition_context=context_for(goals['definition_context'],g))
        obj=semantic_entry(law);i=identity(obj);pure_objects[i]=obj;pure_roots.append(i);names['contract.'+g['name']]=i
        proofs[g['name']]={'Use':dict(law=i,arguments={n:dict(sort=t,node={'Free':n}) for n,t in g['params'].items()},premises=[{'Hypothesis':j} for j in range(len(g['conditions']))])}
    def add(declaration):
        d=declaration['Theorem'];deps=references(declaration);pending=list(deps)
        while pending:
            for dep in state_objects[pending.pop()]['dependencies']:
                if dep not in deps:deps.add(dep);pending.append(dep)
        obj=entry('theorem',MATH,dict(declaration=declaration),deps,parameters=dict(d['params']),conditions=d['conditions']);i=identity(obj);state_objects[i]=obj;return i
    for number,g in enumerate((goals['state'] or {}).get('obligations',[])):
        from producers.point_delta import free_variables
        a,z=g['goal']['from'],g['goal']['to'];all_conditions=g['conditions']
        data_names={n for n,t in g['params'] if isinstance(t,dict) and 'Data' in t}
        subsets=[list(range(len(all_conditions))),[i for i,c in enumerate(all_conditions) if not ((free_variables(c['from'])|free_variables(c['to'])) & data_names)],[]]
        success=False;errors=[]
        for attempt,indices in enumerate(subsets):
            conditions=[all_conditions[i] for i in indices];hyp=[(c['from'],c['to'],i) for i,c in enumerate(conditions)]
            try:
                if indices==list(range(len(all_conditions))):
                    proof=next((p for p in [convert(a,z),*[{'Hypothesis':i} for i in range(len(hyp))]] if check(g,p)),None)
                else:proof=None
                if proof is None:proof=state_proof(state_objects,a,z,dict(g['params']),hyp)
            except ValueError as error:errors.append(str(error));continue
            i=add({'Theorem':dict(params=g['params'],conditions=conditions,**g['goal'],proof=proof)})
            trial=Store.publish(directory/'trials'/f'{number}-{attempt}',state_objects.values())
            use={'Use':dict(theorem=i,arguments=[var(n) for n,_ in g['params']],premises=[{'Hypothesis':j} for j in indices])}
            if check(g,use,trial.bundle([i])):
                state_roots.append(i);names['contract.'+g['name']]=i;state_proofs[g['name']]=use;success=True;break
            state_objects.pop(i)
        if not success:raise ValueError('no checked state proof for '+g['name']+': '+'; '.join(errors)[-1200:])
    store=Store.publish(directory,[*pure_objects.values(),*state_objects.values()],names)
    evidence=dict(schema=1,semantics=goals['semantics'],source_sha256=goals['source_sha256'],proofs=proofs,state_proofs=state_proofs,knowledge=store.bundle(pure_roots) if pure_roots else None,state_knowledge=store.bundle(state_roots) if state_roots else None)
    target=directory/'evidence.json';target.write_text(json.dumps(evidence,separators=(',',':'))+'\n')
    if not bodies:subprocess.run([compiler,'check-contracts',source,'--contract-proofs',str(target),*(['--core'] if Path(source).suffix=='.json' else [])],check=True,capture_output=True,text=True)
    return evidence,store

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source');p.add_argument('output');p.add_argument('--compiler',required=True);p.add_argument('--bodies');p.add_argument('--source-evidence');a=p.parse_args()
    author(a.compiler,a.source,a.output,a.bodies,a.source_evidence)
    print('Checked contract evidence and canonical entries:',a.output)
if __name__=='__main__':main()
