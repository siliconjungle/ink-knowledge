"""External proposals for factorised word aggregates on arbitrary source rows.

Admission proves the exact source observation and commutative group laws.
Schema names, producer patterns and workload profiles grant no authority.
"""
import argparse, copy, json, subprocess, tempfile, os
from pathlib import Path
from ink_knowledge import Store, identity, canonical
from ink_knowledge.store import entry
from producers.action_replacement import var, call, cons, convert, trans
from producers.point_delta import binary
from producers.representations import refs, match
from producers.state_laws import derive
from producers.workspace import compiler_path

def invoke(compiler,*args):
    result=subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=180)
    if result.returncode:raise ValueError(result.stderr.strip())
    return result.stdout

def publish(plan,root):
    """Publish ordinary source-bound candidates; admission still replays proofs."""
    package=plan['steps'][0]['package']
    objects=package['knowledge']['objects']
    roots={i for i,o in objects.items()if o['kind']!='theorem'}|refs(package['views'])
    compact={k:v for k,v in package.items()if k!='knowledge'}
    compact['knowledge_ref']=dict(roots=sorted(roots))
    candidate=entry('maintenance','ink-maintained-fold-v1',dict(package=compact),roots)
    store=Store(root).extend([*objects.values(),candidate])
    return dict(entry=identity(candidate),snapshot=store.snapshot_id,roots=len(roots))

def produce(source,compiler,directory,keeps=None,capacity=0,source_core=False):
    source=Path(source).resolve();compiler=Path(compiler).resolve();directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    flags=['--core']if source_core else []
    with tempfile.TemporaryDirectory(prefix='ink-maintained-folds-')as temporary:
        temp=Path(temporary);subjects_path=temp/'subjects.json';model_path=temp/'model.json'
        invoke(compiler,'emit-maintained-subjects',source,*flags,'-o',subjects_path)
        invoke(compiler,'emit-action-model',source,*flags,'-o',model_path)
        subjects=json.loads(subjects_path.read_bytes());model=json.loads(model_path.read_bytes())
        objects={**model['objects'],**subjects['objects']};declined=[];views=[]
        def add(decl,extra=()):
            payload=dict(declaration=decl);body=next(iter(decl.values()))
            obj=entry('theorem'if'Theorem'in decl else'definition','first-order-inductive-equality-v1',payload,refs(payload)|set(extra),parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]))
            i=identity(obj);objects[i]=obj;return i
        from producers.word_ring import Tactic
        ring=Tactic(add,compiler)
        combine=add({'Function':dict(params=[['a','U64'],['b','U64']],result='U64',body=binary('+',var('a'),var('b')),recursive=None)})
        inverse=add({'Function':dict(params=[['a','U64']],result='U64',body=binary('-',{'U64':0},var('a')),recursive=None)})
        zero={'U64':0}
        # Ordinary checked word laws include all 64 bits and wrapping arithmetic.
        c=lambda a,b:call(combine,[a,b])
        def scalar(left,right,proof):
            from producers.point_delta import normal
            return trans(convert(left,normal(left,objects)),proof,convert(normal(right,objects),right))
        group=dict(identity=scalar(c(zero,var('a')),var('a'),ring.law('left_zero',[var('a')])),
            associativity=scalar(c(c(var('a'),var('b')),var('c')),c(var('a'),c(var('b'),var('c'))),ring.law('assoc',[var('a'),var('b'),var('c')])),
            commutativity=scalar(c(var('a'),var('b')),c(var('b'),var('a')),ring.law('commute',[var('a'),var('b')])),
            cancellation=scalar(c(call(inverse,[var('a')]),var('a')),zero,ring.prove(binary('+',binary('-',zero,var('a')),var('a')),zero)))
        from producers.aggregate_delta import setup
        for subject in subjects['subjects']:
            if keeps is not None and subject['keep']not in keeps:continue
            if subject['result']!='U64':
                declined.append(dict(keep=subject['keep'],reason='this producer authors wrapping word groups; other groups need their own proofs'));continue
            if subject['key']!='U64':
                declined.append(dict(keep=subject['keep'],reason='this fold tactic currently requires word keys; other key codecs need their own source proofs'));continue
            try:
                root=subject['root'];table=model['tables'][root]
                local={**model,'tables':[table],'objects':objects}
                cache=dict(case=dict(bindings=[subject['bindings'][root]],normal={'Construct':dict(datatype='',constructor=0,arguments=[subject['value']])}))
                delta=setup(local,cache,add,objects,specialized=True)
                contribution=add({'Function':dict(params=[['key',subject['key']],['row',subject['row']]],result='U64',body=call(delta['contribution'],[var('row')]),recursive=None)})
                fold=add({'Function':dict(params=[['rows',{'Data':subject['rows']}]],result='U64',recursive=0,body=match(var('rows'),[
                    ([],zero),(['key','row','tail'],c(call(contribution,[var('key'),var('row')]),{'SelfCall':[var('tail')]}))
                ]))},[subject['rows'],contribution,combine])
                # The fixed fold's dependency set is part of its carrier meaning.
                exact=entry('definition','first-order-inductive-equality-v1',objects[fold]['payload'],sorted({subject['rows'],contribution,combine}),parameters={'rows':{'Data':subject['rows']}},result='U64')
                del objects[fold];fold=identity(exact);objects[fold]=exact
                xs=var('rows');old=lambda x:call(delta['fold'],[x]);new=lambda x:call(fold,[x])
                nil=cons(subject['rows'],0,[]);node=cons(subject['rows'],1,[var('key'),var('row'),var('tail')])
                proof={'Induction':dict(variable='rows',**{'from':old(xs),'to':new(xs)},cases=[
                    dict(bindings=[],proof=convert(old(nil),new(nil))),
                    dict(bindings=['key','row','tail'],proof=derive(old(node),new(node),objects,[(old(var('tail')),new(var('tail')))]))
                ])}
                lemma=add({'Theorem':dict(params=[['rows',{'Data':subject['rows']}]],conditions=[],**{'from':old(xs),'to':new(xs)},proof=proof)},[i for i,o in objects.items()if 'Datatype'in o['payload'].get('declaration',{})])
                actual=var(subject['bindings'][root])
                factorisation=trans(delta['fusion_proof'](actual),{'Use':dict(theorem=lemma,arguments=[actual],premises=[])})
                from producers.point_delta import normal
                row_contribution=lambda row:call(contribution,[var('key'),row])
                node=lambda row:cons(subject['rows'],1,[var('key'),row,var('tail')])
                total=lambda xs:call(fold,[xs])
                old=row_contribution(var('row'));neg=call(inverse,[old])
                def mutation(left,right):
                    a,z=normal(left,objects),normal(right,objects)
                    return trans(convert(left,a),delta['prove_arithmetic'](a,z),convert(z,right))
                mutations=dict(
                    insertion=mutation(c(total(var('tail')),old),total(node(var('row')))),
                    deletion=mutation(c(total(node(var('row'))),neg),total(var('tail'))),
                    replacement=mutation(c(total(node(var('row'))),c(neg,row_contribution(var('new')))),total(node(var('new'))))
                )
                views.append(dict(keep=subject['keep'],table=subject['table'],contribution=contribution,combine=combine,inverse=inverse,zero=zero,factorisation=factorisation,**group,**mutations))
            except (ValueError,KeyError)as e:
                if os.environ.get('INK_PROOF_DEBUG'):raise
                declined.append(dict(keep=subject['keep'],reason=str(e)))
        if not views:raise ValueError('no factorised folds authored: '+str(declined))
        store=Store.publish(directory/'knowledge',list(objects.values()))
        package=dict(schema=1,semantics='ink-maintained-fold-v1',input_core_sha256=subjects['source'],knowledge=store.bundle(sorted(objects)),views=views)
        steps=[dict(kind='maintained',package=package)]
        if capacity:
            physical=dict(schema=1,semantics='ink-physical-plan-v1',input_core_sha256=subjects['source'],dense_prefixes=[dict(table=n,capacity=capacity)for n in sorted({v['table']for v in views})])
            steps.append(dict(kind='physical',package=physical))
        plan=dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=subjects['source'],steps=steps)
        path=directory/'plan.json';path.write_bytes(canonical(plan)+b'\n')
        invoke(compiler,'check-plan',source,path,*flags)
        (directory/'production.json').write_text(json.dumps(dict(source=subjects['source'],views=len(views),declined=declined),indent=2)+'\n')
        return plan

def candidates(context):
    if context.get('representation')or context.get('maintained')or context.get('emit_target')!='javascript':
        yield dict(status='declined',label='maintained-folds',reason='requires JavaScript source state capability');return
    with tempfile.TemporaryDirectory(prefix='ink-maintained-candidates-')as temporary:
        temp=Path(temporary);source=temp/'source.json';source.write_bytes(canonical(context['core']))
        try:
            plan=produce(source,context['compiler'],temp/'map',source_core=True)
            yield dict(status='proposal',label='maintained-folds/map',steps=plan['steps'])
            capacities=context.get('dense_capacities',[256,4096])
            for capacity in capacities:
                if type(capacity)is not int or not 1<=capacity<=1048576:continue
                physical=dict(schema=1,semantics='ink-physical-plan-v1',input_core_sha256=plan['input_core_sha256'],dense_prefixes=[dict(table=n,capacity=capacity)for n in sorted({v['table']for v in plan['steps'][0]['package']['views']})])
                yield dict(status='proposal',label='maintained-folds/dense-prefix-'+str(capacity),steps=[*plan['steps'],dict(kind='physical',package=physical)])
        except (ValueError,subprocess.TimeoutExpired)as e:yield dict(status='declined',label='maintained-folds',reason=str(e))

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source',type=Path);p.add_argument('-o',type=Path,required=True);p.add_argument('--compiler',type=Path,default=compiler_path());p.add_argument('--keep',action='append');p.add_argument('--dense-capacity',type=int,default=0);p.add_argument('--core',action='store_true');p.add_argument('--publish',type=Path);a=p.parse_args()
    plan=produce(a.source,a.compiler,a.o,a.keep,a.dense_capacity,a.core)
    if a.publish:print(json.dumps(publish(plan,a.publish)))
if __name__=='__main__':main()
