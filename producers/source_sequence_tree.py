#!/usr/bin/env python3
"""Propose source-bound indexed sequences using ordinary knowledge proofs.

The producer has no admission authority. All row order, duplicate-key, cached
aggregate, transaction, snapshot and migration equations require kernel replay.
"""
import argparse,copy,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,identity
from ink_knowledge.store import entry
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import match,binary,sub
from producers.representations import refs,REP,MATH
from producers.sequence_tree import define,D
from producers.sequence_tree_proofs import prove

def generate(model,directory,cache_query=None):
    if len(model['tables'])!=1:raise ValueError('indexed sequence authoring currently requires one table')
    objects=copy.deepcopy(model['objects'])
    carriers=[i for i,o in objects.items()if 'Datatype'in o['payload'].get('declaration',{})]
    def add(declaration,extra=()):
        declaration=copy.deepcopy(declaration);body=next(iter(declaration.values()))
        dependencies=refs(declaration)|set(extra)
        if 'Datatype'not in declaration:dependencies|=set(carriers)
        e=entry('theorem'if 'Theorem'in declaration else'definition',MATH,{'declaration':declaration},dependencies,parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]))
        key=identity(e);objects[key]=e
        if 'Datatype'in declaration:carriers.append(key)
        return key
    def fn(params,result,body):return add({'Function':dict(params=params,result=result,body=body,recursive=None)})
    table=model['tables'][0];table_id=table['datatype'];L=D(model['state'])
    row_sort=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    option=objects[table['get']]['payload']['declaration']['Function']['result']['Data']
    aggregate=None
    if cache_query:
        from producers.aggregate_delta import setup
        aggregate=setup(model,model['actions'][cache_query],add,objects)
    names=define(table_id,row_sort,option,add,aggregate['contribution']if aggregate else None)
    names.update(table=table_id,option=option)
    tactic=prove(names,objects,add,row_sort)
    f=lambda name,*xs:call(names[name],list(xs))
    tree_sort=D(names['datatype']);t,k,v=map(var,['tree','key','value']);valid=lambda t:f('valid',t)
    guard=dict(**{'from':valid(t),'to':{'Bool':True}})
    # The source operations are independent fixed definitions. These bridges
    # relate them to the list definitions already proved against the tree.
    for op in ['get','insert','replace','remove']:
        extras=[]if op in ['get','remove']else[v]
        params=[['rows',D(table_id)],['key','U64']]+([]if not extras else[['value',row_sort]])
        rows=var('rows');a=call(table[op],[rows,k,*extras]);z=f('rows_'+op,rows,k,*extras)
        names['source-'+op]=tactic.theorem('source-'+op,params,a,z,'rows')
        a=call(table[op],[f('decode',t),k,*extras]);z=f('get',t,k)if op=='get'else f('decode',f(op,t,k,*extras))
        bridge={'Use':dict(theorem=names['source-'+op],arguments=[f('decode',t),k,*extras],premises=[])}
        if op=='get':
            proof=trans(bridge,{'Use':dict(theorem=names['find-order'],arguments=[t,k],premises=[])},{'Sym':{'Use':dict(theorem=names['get-find'],arguments=[t,k],premises=[{'Hypothesis':0}])}})
        else:proof=trans(bridge,{'Use':dict(theorem=names[op+'-order'],arguments=[t,k,*extras],premises=[{'Hypothesis':0}])})
        theorem=add({'Theorem':dict(params=[['tree',tree_sort],['key','U64']]+([]if not extras else[['value',row_sort]]),conditions=[guard],**{'from':a,'to':z},proof=proof)})
        names['source-'+op+'-tree']=theorem;tactic.register(theorem)
    if aggregate:
        from producers.word_ring import Tactic as WordTactic
        from producers.scalar_tactic import Scalar
        ring=WordTactic(add,tactic.scalar.compiler);memo={}
        def arithmetic(a,z):
            opaque=[]
            def abstract(t):
                if 'U64'in t:return t
                if 'Binary'in t and t['Binary']['op']in ['+','-','*']:
                    x=t['Binary'];return binary(x['op'],abstract(x['left']),abstract(x['right']))
                if t not in opaque:opaque.append(t)
                return var('word_'+str(opaque.index(t)))
            aa,zz=abstract(a),abstract(z);key=json.dumps([aa,zz],sort_keys=True)
            if key not in memo:
                p=ring.prove(aa,zz);memo[key]=add({'Theorem':dict(params=[['word_'+str(i),'U64']for i in range(len(opaque))],conditions=[],**{'from':aa,'to':zz},proof=p)})
            return {'Use':dict(theorem=memo[key],arguments=opaque,premises=[])}
        tactic.arithmetic=arithmetic
        total=lambda xs:call(aggregate['fold'],[xs]);xs,ys=map(var,['xs','ys'])
        names['fold-append']=tactic.theorem('fold-append',[['xs',D(table_id)],['ys',D(table_id)]],total(f('append',xs,ys)),binary('+',total(xs),total(ys)),'xs')
        names['fold-measure']=tactic.theorem('fold-measure',[['tree',tree_sort]],total(f('decode',t)),f('measure',t),'tree',guard=f('measure_valid',t))
        query=model['actions'][cache_query]['case'];query_term=query['normal']['Construct']['arguments'][0]
        source_q=lambda xs:sub(query_term,{query['bindings'][0]:xs})
        fusion={'Use':dict(theorem=aggregate['fusion'],arguments=[f('decode',t)],premises=[])}
        measure_premise=tactic.equality(f('measure_valid',t),{'Bool':True},{'tree':tree_sort},facts=[(valid(t),{'Bool':True},{'Hypothesis':0})],hypotheses=1)
        theorem=add({'Theorem':dict(params=[['tree',tree_sort]],conditions=[guard],**{'from':source_q(f('decode',t)),'to':f('measure',t)},proof=trans(fusion,{'Use':dict(theorem=names['fold-measure'],arguments=[t],premises=[measure_premise])}))})
        names['source-query-tree']=theorem;tactic.register(theorem)
    else:query_term=None
    Pid=add({'Datatype':dict(constructors=[dict(name='Indexed',fields=[tree_sort])])});P=D(Pid)
    logical_root=lambda xs:cons(model['state'],0,[xs]);physical_root=lambda root:cons(Pid,0,[root])
    encode=fn([['logical',L]],P,match(var('logical'),[(['rows'],physical_root(f('encode',var('rows'))))]))
    decode=fn([['physical',P]],L,match(var('physical'),[(['tree'],logical_root(f('decode',t)))]))
    validity=fn([['physical',P]],'Bool',match(var('physical'),[(['tree'],valid(t))]))
    relation0=fn([['physical',P],['logical',L]],L,call(decode,[var('physical')]))
    relation0r=fn([['physical',P],['logical',L]],L,var('logical'))
    relation1=fn([['physical',P],['logical',L]],'Bool',call(validity,[var('physical')]))
    relation1r=fn([['physical',P],['logical',L]],'Bool',{'Bool':True})
    tactic.cases_first=True
    init0=tactic.equality(call(decode,[call(encode,[var('logical')])]),var('logical'),{'logical':L})
    init1=tactic.equality(call(validity,[call(encode,[var('logical')])]),{'Bool':True},{'logical':L})
    actions={}
    mapping={table[op]:op for op in ['get','insert','replace','remove']}
    for name,source in model['actions'].items():
        source_result=source['result']['Data'];constructors=objects[source_result]['payload']['declaration']['Datatype']['constructors']
        pc=copy.deepcopy(constructors);pc[0]['fields'][3]=P;pc[1]['fields'][2]=P
        result_id=add({'Datatype':dict(constructors=pc)});result=D(result_id)
        case=source['case'];root_name=case['bindings'][0]
        def translate(term):
            if term==var(root_name):return t
            if query_term is not None and name==cache_query and term==query_term:return f('measure',t)
            if 'Construct'in term:
                x=term['Construct'];args=[translate(a)for a in x['arguments']]
                if x['datatype']==model['state']:return physical_root(args[0])
                if x['datatype']==source_result:return cons(result_id,x['constructor'],args)
                if x['datatype']==table_id:raise ValueError('source list construction needs an authored encode bridge')
                return cons(x['datatype'],x['constructor'],args)
            if 'Call'in term:
                x=term['Call'];args=[translate(a)for a in x['arguments']]
                if x['function']in mapping:return f(mapping[x['function']],*args)
                d=objects[x['function']]['payload']['declaration']['Function']
                args=[f('decode',a)if sort==D(table_id)else a for a,(_,sort)in zip(args,d['params'])]
                return call(x['function'],args)
            if 'Match'in term:
                x=term['Match'];return match(translate(x['scrutinee']),[(b['bindings'],translate(b['body']))for b in x['branches']])
            if 'If'in term:return {'If':{k:translate(a)for k,a in term['If'].items()}}
            if 'Binary'in term:
                x=term['Binary'];return binary(x['op'],translate(x['left']),translate(x['right']))
            return copy.deepcopy(term)
        rest=source['params'][1:];args=[var(n)for n,_ in rest]
        body=match(var('initial'),[(['tree'],translate(case['normal']))])
        execute=fn([['initial',P],*rest],result,body)
        success=['reply','committed','post_version','post_physical','events'];failure=['host','post_version','post_physical']
        nextf=fn([['outcome',result]],P,match(var('outcome'),[(success,var('post_physical')),(failure,var('post_physical'))]))
        observe=fn([['outcome',result]],D(source_result),match(var('outcome'),[(success,cons(source_result,0,[var('reply'),var('committed'),var('post_version'),call(decode,[var('post_physical')]),var('events')])),(failure,cons(source_result,1,[var('host'),var('post_version'),call(decode,[var('post_physical')])]))]))
        physical=var('physical');executed=call(execute,[physical,*args]);original_decoded=call(source['function'],[call(decode,[physical]),*args])
        env={'physical':P,**dict(rest)};facts=[(call(validity,[physical]),{'Bool':True},{'Hypothesis':0})]
        observed=call(observe,[executed])
        equality=tactic.equality(observed,original_decoded,env,facts=facts,hypotheses=1)
        law=add({'Theorem':dict(params=[['physical',P],*rest],conditions=[dict(**{'from':call(validity,[physical]),'to':{'Bool':True}})],**{'from':observed,'to':original_decoded},proof=equality)})
        original=call(source['function'],[var('logical'),*args])
        observation=trans({'Use':dict(theorem=law,arguments=[physical,*args],premises=[{'Hypothesis':1}])},{'Substitute':dict(variable='source_state_hole',context=call(source['function'],[var('source_state_hole'),*args]),equality={'Hypothesis':0})})
        post=lambda value:match(value,[(success, var('post_physical')),(failure,var('post_physical'))])
        # The portable post-state projection is checked separately from replies.
        post_source=lambda value:match(value,[(['reply','committed','post_version','post_rows','events'],var('post_rows')),(['host','post_version','post_rows'],var('post_rows'))])
        outcome=var('outcome')
        pa=call(decode,[call(nextf,[outcome])]);pz=post_source(call(observe,[outcome]))
        post_law=add({'Theorem':dict(params=[['outcome',result]],conditions=[],**{'from':pa,'to':pz},proof=tactic.equality(pa,pz,{'outcome':result}))})
        post_bridge={'Use':dict(theorem=post_law,arguments=[executed],premises=[])}
        preservation0=trans(post_bridge,{'Substitute':dict(variable='source_outcome_hole',context=post_source(var('source_outcome_hole')),equality=observation)})
        preservation1=tactic.equality(call(validity,[call(nextf,[executed])]),{'Bool':True},env,facts=facts,hypotheses=1)
        # Its only premise is the second relation in the enclosing obligation.
        preservation1={'Use':dict(theorem=add({'Theorem':dict(params=[['physical',P],*rest],conditions=[dict(**{'from':call(validity,[physical]),'to':{'Bool':True}})],**{'from':call(validity,[call(nextf,[executed])]),'to':{'Bool':True}},proof=preservation1)}),arguments=[physical,*args],premises=[{'Hypothesis':1}])}
        actions[name]=dict(execute=execute,result=result,next=nextf,observe=observe,preservation=[preservation0,preservation1],observation=observation)
    plan=dict(source_objects=sorted(model['objects']),logical_state=L,physical_state=P,encode=encode,decode=decode,relations=[dict(left=relation0,right=relation0r),dict(left=relation1,right=relation1r)],initialisation=[init0,init1],snapshot={'Hypothesis':0},actions=actions)
    e=entry('representation',REP,plan,refs(plan),parameters={'logical':L},result=P,effects=['source-transitions']);e['interface']['operations']=sorted(actions);rid=identity(e);objects[rid]=e
    pending=[rid];reachable=set()
    while pending:
        i=pending.pop()
        if i in reachable:continue
        reachable.add(i);pending.extend(objects[i]['dependencies'])
    store=Store.publish(directory,[objects[i]for i in sorted(reachable)],{'indexed-sequence':rid})
    request=dict(schema=1,semantics=REP,input_core_sha256=model['source'],knowledge=store.bundle([rid]),representation=rid)
    from producers.compact_observation import attach as compact
    return compact(request,Path(directory)/'compact')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('model',type=Path);p.add_argument('-o','--output',type=Path,required=True);p.add_argument('--cache-query');a=p.parse_args()
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(generate(json.loads(a.model.read_text()),a.output.parent/'database',a.cache_query),separators=(',',':'))+'\n')
