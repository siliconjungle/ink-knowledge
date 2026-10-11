#!/usr/bin/env python3
"""Propose a source-bound stable partition index, checked by ordinary equations.

An enumeration spine retains arbitrary order and duplicates. Lookup selects one
stable bucket; every source observation remains explicit. Unsupported mutations
refresh the buckets. No executable optimisation authority comes from this script.
"""
import argparse,json,sys,subprocess,tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from ink_knowledge import Store,identity
from ink_knowledge.store import entry
from producers.state_calculus import CanonicalLibrary
from producers.indexed_state_laws import build as index_laws
from producers.general_laws import var,call,construct,match,refl,hyp,trans,use,sym,substitute,references,congruence
from producers.point_delta import binary,sub,normal,replace
from producers.action_replacement import convert
from producers.representations import refs,unchanged_query
from producers.cache_maintenance import cases
from producers.workspace import compiler_path

def partition(x):return binary('==',binary('&',x,{'U64':1}),{'U64':0})

def congruence_certificate():
    q,h=var('query'),var('head')
    goal=dict(params=[['query','U64'],['head','U64']],conditions=[dict(**{'from':binary('==',q,h),'to':{'Bool':True}})],**{'from':partition(q),'to':partition(h)})
    cache=Path(__file__).resolve().parents[1]/'research/composable-state/partition-even-certificate.json'
    if cache.exists():
        value=json.loads(cache.read_text())
        if value['goal']!=goal:raise ValueError('partition certificate goal mismatch')
        return value['certificate']
    from bitvector_proofs import certificate
    with tempfile.TemporaryDirectory(prefix='ink-partition-proof-')as tmp:
        a=Path(tmp)/'goal.json';b=Path(tmp)/'cnf.json';a.write_text(json.dumps(goal))
        subprocess.run([str(compiler_path()),'bitvector-obligation',str(a),'-o',str(b)],check=True,capture_output=True)
        proof=certificate(json.loads(b.read_text()))
    cache.parent.mkdir(parents=True,exist_ok=True);cache.write_text(json.dumps(dict(goal=goal,certificate=proof),separators=(',',':'))+'\n')
    return proof

class ConcreteIndex(CanonicalLibrary):
    def __init__(self,model,table):
        super().__init__();self.objects=dict(model['objects']);self.table=table
    def sort(self,name):
        if name=='IndexedRow':return self.objects[self.table['replace']]['payload']['declaration']['Function']['params'][2][1]
        return super().sort(name)
    def abstract(self,name,params,result):
        if name=='key_partition':return self.function(name,[['key','U64']],'Bool',partition(var('key')))
        return super().abstract(name,params,result)
    def store(self,name,kind,declaration,extra=()):
        source={'IndexedRows':self.table['datatype'],'IndexedOption':self.objects[self.table['get']]['payload']['declaration']['Function']['result']['Data'],
                'indexed_source_get':self.table['get'],'indexed_source_remove':self.table['remove'],'indexed_source_replace':self.table['replace']}
        if name in source:self.names[name]=source[name];return source[name]
        if name=='equal_keys_have_equal_partition':
            a,z=declaration['from'],declaration['to'];na,nz=partition(var('query')),partition(var('head'))
            declaration={**declaration,'proof':trans(convert(a,na),{'BitVector':dict(**{'from':na,'to':nz},hypotheses=[0],certificate=congruence_certificate())},convert(nz,z))};kind='Theorem'
        # Inferred Match scrutinee sorts are still explicit canonical context
        # dependencies. Include all existing concrete carrier declarations.
        carriers=[i for i,e in self.objects.items()if 'Datatype'in e['payload'].get('declaration',{})]
        return super().store(name,kind,declaration,[*extra,*carriers])

def generate(model,directory,table_index=0):
    if not 0<=table_index<len(model['tables']):raise ValueError('table index out of range')
    table=model['tables'][table_index]
    if model['objects'][table['get']]['payload']['declaration']['Function']['params'][1][1]!='U64':raise ValueError('partition producer requires u64 keys')
    lib=ConcreteIndex(model,table);index_laws(lib);n=lib.names;objects=lib.objects
    L={'Data':model['state']};fields=objects[model['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields'];roots=['root_'+str(i)for i in range(len(fields))]
    # Match the physical table by its datatype rather than source declaration
    # position: source projection may reorder roots canonically.
    candidates=[i for i,f in enumerate(fields)if f=={'Data':table['datatype']}]
    if len(candidates)!=1:raise ValueError('ambiguous source table root')
    index=candidates[0];root=var(roots[index]);IS={'Data':n['PartitionIndex']}
    Pid=lib.store('SourceIndexedState','Datatype',dict(constructors=[dict(name='State',fields=fields+[IS])]))
    P={'Data':Pid};pn=roots+['index']
    decision=lib.store('IndexRepairDecision','Datatype',dict(constructors=[dict(name='Refresh',fields=[]),dict(name='Ready',fields=[IS])]))
    DS={'Data':decision}
    encode=lib.function('source_encode',[['logical',L]],P,match(var('logical'),(roots,construct(Pid,0,*map(var,roots),call(n['partition_encode'],root)))))
    decode=lib.function('source_decode',[['physical',P]],L,match(var('physical'),(pn,construct(model['state'],0,*map(var,roots)))))
    bound=construct(model['state'],0,*map(var,roots))
    a=call(decode,call(encode,var('logical')));z=var('logical')
    roundtrip=lib.theorem('source_roundtrip',[['logical',L]],a,z,{'Induction':dict(variable='logical',**{'from':a,'to':z},cases=[dict(bindings=roots,proof=convert(call(decode,call(encode,bound)),bound))])})
    left=lib.function('relation_left',[['physical',P],['logical',L]],P,var('physical'))
    right=lib.function('relation_right',[['physical',P],['logical',L]],P,call(encode,var('logical')))
    relation=lambda p,l:(call(left,p,l),call(right,p,l))
    snapshot=trans(convert(call(decode,var('physical')),call(decode,relation(var('physical'),var('logical'))[0])),substitute('hole',call(decode,var('hole')),hyp(0)),use(roundtrip,var('logical')))
    def rewrite(term,binding):
        if isinstance(term,list):return [rewrite(x,binding)for x in term]
        if not isinstance(term,dict):return term
        c=term.get('Call',{})
        if c.get('function')==table['get'] and c['arguments'][0]==var(binding):return call(n['partition_lookup'],var('index'),rewrite(c['arguments'][1],binding))
        return {k:rewrite(v,binding)for k,v in term.items()}
    def reads(term,binding):
        if isinstance(term,list):return [x for t in term for x in reads(t,binding)]
        if not isinstance(term,dict):return []
        c=term.get('Call',{})
        found=[c['arguments'][1]]if c.get('function')==table['get'] and c['arguments'][0]==var(binding) else []
        return found+[x for t in term.values()for x in reads(t,binding)]
    def recipe(rows,initial):
        if rows==root:return initial
        c=rows.get('Call',{});args=c.get('arguments',[])
        operation=next((op for op in ('remove','replace')if table[op]==c.get('function')),None)
        if operation is None:raise ValueError('index mutation refresh required')
        return call(n['partition_repair_'+operation],recipe(args[0],initial),*args[1:])
    def recipe_proof(rows):
        if rows==root:return refl(call(n['partition_encode'],root))
        c=rows['Call'];args=c['arguments'];operation=next(op for op in ('remove','replace')if table[op]==c['function'])
        fn=n['partition_repair_'+operation]
        return trans(congruence(fn,recipe_proof(args[0]),*[refl(a)for a in args[1:]]),use(n['partition_repair_'+operation+'_exact'],*args))
    def factor_cases(proof,params,conditions=()):
        # Each source branch is checked as a bounded closed conditional lemma;
        # composition never raises the kernel work limit.
        if 'BoolSplit'in proof:
            x=proof['BoolSplit'];branches={}
            for key,flag in [('on_false',False),('on_true',True)]:
                premise={'from':x['condition'],'to':{'Bool':flag}}
                branches[key]=factor_cases(x[key],params,(*conditions,premise))
            lemma=lib.store('index_case_'+str(len(objects)),'Theorem',dict(params=params,conditions=list(conditions),**{k:x[k]for k in ('from','to')},proof={'BoolSplit':{**x,**branches}}))
            return {'Use':dict(theorem=lemma,arguments=[var(n)for n,_ in params],premises=[hyp(i)for i in range(len(conditions))])}
        if 'Trans'in proof:return {'Trans':[factor_cases(p,params,conditions)for p in proof['Trans']]}
        if 'Sym'in proof:return {'Sym':factor_cases(proof['Sym'],params,conditions)}
        if 'Substitute'in proof:return {'Substitute':{**proof['Substitute'],'equality':factor_cases(proof['Substitute']['equality'],params,conditions)}}
        return proof
    actions={}
    for name,action in model['actions'].items():
        rest=action['params'][1:];args=[var(v)for v,_ in rest];mapping=dict(zip(action['case']['bindings'],map(var,roots)))
        original=call(action['function'],var('logical'),*args)
        source_normal=sub(action['case']['normal'],mapping)
        retain=unchanged_query(model,action)
        if retain:
            pair=lib.store('Retained_'+name,'Datatype',dict(constructors=[dict(name='Retained',fields=[P,action['result']])]))
            decorate=lambda term,initial:construct(pair,0,var('initial'),term)
            body=construct(pair,0,var('initial'),source_normal)
        else:
            pair=lib.store('Repaired_'+name,'Datatype',dict(constructors=[dict(name='Repaired',fields=[DS,action['result']])]))
            def decorate(term,initial):
                if 'If'in term:
                    x=term['If'];return {'If':dict(condition=x['condition'],on_true=decorate(x['on_true'],initial),on_false=decorate(x['on_false'],initial))}
                obs=term['Construct'];args=obs['arguments']
                change=construct(decision,1,initial)
                if obs['constructor']==0 and args[1]=={'Bool':True}:
                    updated=args[3]['Construct']['arguments'][index]
                    try:change=construct(decision,1,recipe(updated,initial))
                    except ValueError:change=construct(decision,0)
                return construct(pair,0,change,term)
            body=decorate(source_normal,var('index'))
        result={'Data':pair}
        # Rewrite the already decorated observation so its guards are evaluated
        # once, shared by the source reply and the index repair decision.
        body=rewrite(body,roots[index])
        execute=lib.function('execute_'+name,[['initial',P]]+rest,result,match(var('initial'),(pn,body)))
        observe=lib.function('observe_'+name,[['observed',result]],action['result'],match(var('observed'),(['retained'if retain else'index_change','reply'],var('reply'))))
        post=lambda x:match(x,(['index_reply','index_committed','index_version','index_state','index_events'],var('index_state')),(['index_host','index_version','index_state'],var('index_state')))
        new_roots=['post_root_'+str(i)for i in range(len(fields))]
        restored=match(post(var('reply')),(new_roots,construct(Pid,0,*map(var,new_roots),var('ready_index'))))
        next_body=match(var('observed'),(['retained','reply'],var('retained')))if retain else match(var('observed'),(['index_change','reply'],match(var('index_change'),([],call(encode,post(var('reply')))),(['ready_index'],restored))))
        nextf=lib.function('next_'+name,[['observed',result]],P,next_body,extra=[model['state']])
        selected=call(observe,call(execute,call(encode,bound),*args));expected=call(action['function'],bound,*args)
        # Each replacement is an independently proved lookup equation lifted
        # through the complete observation, including guards, replies and events.
        def lookup_rewrites(term):
            current=normal(term,objects);proof=convert(term,current)
            for query in reads(action['case']['normal'],action['case']['bindings'][index]):
                query=sub(query,mapping)
                start=normal(call(n['partition_lookup'],call(n['partition_encode'],root),query),objects);end=call(table['get'],root,query)
                rewritten=replace(current,start,end)
                if rewritten!=current:
                    law=trans(convert(start,call(n['partition_lookup'],call(n['partition_encode'],root),query)),use(n['partition_encoded_lookup'],root,query))
                    proof=trans(proof,substitute('hole',replace(current,start,var('hole')),law));current=rewritten
            return current,proof
        current,proof=lookup_rewrites(selected)
        if retain:proof=trans(proof,convert(current,expected))
        else:
            initial=call(n['partition_encode'],root)
            left_obs=lambda obs:call(observe,decorate(obs,initial))
            proof=trans(proof,convert(current,left_obs(source_normal)),factor_cases(cases(source_normal,left_obs,lambda obs:obs),list(zip(roots,fields))+rest),convert(source_normal,expected))
        a=call(observe,call(execute,call(encode,var('logical')),*args));z=original
        eq=lib.theorem('observation_'+name,[['logical',L]]+rest,a,z,{'Induction':dict(variable='logical',**{'from':a,'to':z},cases=[dict(bindings=roots,proof=proof)])},extra=[result['Data']])
        executed=call(execute,var('physical'),*args);observed=call(observe,executed)
        observation=trans(substitute('hole',call(observe,call(execute,var('hole'),*args)),hyp(0)),use(eq,var('logical'),*args))
        before,after=relation(call(nextf,executed),post(original))
        if retain:
            retained=call(nextf,executed);pbound=construct(Pid,0,*map(var,pn))
            retention=lib.theorem('retention_'+name,[['physical',P]]+rest,retained,var('physical'),{'Induction':dict(variable='physical',**{'from':retained,'to':var('physical')},cases=[dict(bindings=pn,proof=convert(call(nextf,call(execute,pbound,*args)),pbound))])})
            preserved=lib.theorem('unchanged_'+name,[['logical',L]]+rest,post(original),var('logical'),{'Induction':dict(variable='logical',**{'from':post(original),'to':var('logical')},cases=[dict(bindings=roots,proof=convert(post(expected),bound))])},extra=[action['result']['Data']])
            preservation=trans(convert(before,retained),use(retention,var('physical'),*args),hyp(0),sym(substitute('hole',call(encode,var('hole')),use(preserved,var('logical'),*args))))
        else:
            initial=call(n['partition_encode'],root)
            left_update=lambda obs:call(nextf,decorate(obs,initial));right_update=lambda obs:call(encode,post(obs))
            def repair_leaf(obs,facts):
                choice=decorate(obs,initial)['Construct']['arguments'][0]['Construct']
                if choice['constructor']==0:return convert(left_update(obs),right_update(obs))
                o=obs['Construct'];state=o['arguments'][3 if o['constructor']==0 else 2]['Construct']['arguments'];updated=state[index]
                candidate=recipe(updated,initial)
                a=construct(Pid,0,*state,candidate);z=construct(Pid,0,*state,call(n['partition_encode'],updated))
                return trans(convert(left_update(obs),a),{'Construct':dict(datatype=Pid,constructor=0,arguments=[refl(r)for r in state]+[recipe_proof(updated)])},convert(z,right_update(obs)))
            update_a=call(nextf,call(execute,call(encode,var('logical')),*args));update_z=call(encode,post(original))
            start=call(nextf,call(execute,call(encode,bound),*args));current,proof=lookup_rewrites(start)
            step=trans(proof,convert(current,left_update(source_normal)),factor_cases(cases(source_normal,left_update,right_update,leaf_proof=repair_leaf),list(zip(roots,fields))+rest),convert(right_update(source_normal),call(encode,post(expected))))
            update_law=lib.theorem('repair_action_'+name,[['logical',L]]+rest,update_a,update_z,{'Induction':dict(variable='logical',**{'from':update_a,'to':update_z},cases=[dict(bindings=roots,proof=step)])},extra=[result['Data']])
            preservation=trans(convert(before,call(nextf,executed)),substitute('hole',call(nextf,call(execute,var('hole'),*args)),hyp(0)),use(update_law,var('logical'),*args),convert(update_z,after))
        actions[name]=dict(execute=execute,result=result,next=nextf,observe=observe,observation=observation,preservation=[preservation])
    ia,iz=relation(call(encode,var('logical')),var('logical'))
    plan=dict(source_objects=sorted(model['objects']),logical_state=L,physical_state=P,encode=encode,decode=decode,relations=[dict(left=left,right=right)],initialisation=[convert(ia,iz)],snapshot=snapshot,actions=actions)
    e=entry('representation','ink-source-representation-v1',plan,refs(plan),parameters={'logical':L},result=P,effects=['source-transitions']);e['interface']['operations']=sorted(actions)
    rid=identity(e);objects[rid]=e
    store=Store.publish(directory,objects.values(),{'representations/partition-index':rid,**{'partition/'+k:v for k,v in n.items()}})
    return dict(schema=1,semantics='ink-source-representation-v1',input_core_sha256=model['source'],knowledge=store.bundle([rid]),representation=rid)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('model',type=Path);p.add_argument('-o','--output',type=Path,required=True);p.add_argument('--table-index',type=int,default=0)
    a=p.parse_args();a.output.parent.mkdir(parents=True,exist_ok=True)
    result=generate(json.loads(a.model.read_text()),a.output.parent/'indexed-database',a.table_index);a.output.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps(dict(status='proposed',representation=result['representation'])))
if __name__=='__main__':main()
