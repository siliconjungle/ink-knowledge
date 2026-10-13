#!/usr/bin/env python3
"""Untrusted compositional repair and shared-fold proofs in canonical knowledge.

Abstract assumptions are obligations, not executable optimisation authority.
Proof::Instance must prove each assumption for the concrete interpretation.
There is no key uniqueness, arithmetic associativity, or event reordering axiom.
"""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,identity
from ink_knowledge.store import entry
from producers.general_laws import (references,var,call,construct,match,self_call,
    refl,hyp,sym,congruence,construct_congruence,use,trans,induction)
MATH='first-order-inductive-equality-v1'

class CanonicalLibrary:
    def __init__(self):self.objects={};self.names={}
    def store(self,name,kind,declaration,extra=()):
        params=dict(declaration.get('params',[]))
        e=entry('theorem' if kind == 'Theorem' else 'definition',MATH,
            {'declaration':{kind:declaration}},references(declaration)|set(extra),parameters=params,
            result=declaration.get('result'),conditions=declaration.get('conditions',[]))
        i=identity(e);self.objects[i]=e;self.names[name]=i;return i
    def sort(self,name):return {'Data':self.store(name,'AbstractSort',dict(name=name))}
    def abstract(self,name,params,result):
        return self.store(name,'AbstractFunction',dict(name=name,params=[[f'argument_{i}',s]for i,s in enumerate(params)],result=result))
    def function(self,name,params,result,body,recursive=None,extra=()):
        return self.store(name,'Function',dict(params=params,result=result,body=body,recursive=recursive),extra)
    def theorem(self,name,params,left,right,proof,extra=()):
        return self.store(name,'Theorem',dict(params=params,conditions=[],**{'from':left,'to':right},proof=proof),extra)
    def assumption(self,name,params,left,right):
        return self.store(name,'Assumption',dict(params=params,conditions=[],**{'from':left,'to':right}))
    def list_of(self,name,element):
        return self.store(name,'Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=[element,'SelfType'])]))

def build(lib):
    S,D,V,E,W=(lib.sort(n)for n in ('State','Change','View','ViewChange','Result'))
    apply=lib.abstract('apply',[S,D],S);query=lib.abstract('query',[S],V)
    repair=lib.abstract('repair',[V,S,D],V)
    view_apply=lib.abstract('view_apply',[V,E],V)
    delta=lib.abstract('view_delta',[S,D],E)
    project=lib.abstract('project',[V],W)
    project_repair=lib.abstract('project_repair',[W,V,E],W)
    s,d,d2,v,e=(var(n)for n in ('state','change','next_change','view','view_change'))
    A=lambda s,d:call(apply,s,d);Q=lambda s:call(query,s)
    R=lambda v,s,d:call(repair,v,s,d);P=lambda v:call(project,v)
    PR=lambda w,v,e:call(project_repair,w,v,e);Delta=lambda s,d:call(delta,s,d)
    qs=Q(s);next_state=A(s,d)
    exact=lib.assumption('repair_exact',[['state',S],['change',D]],R(qs,s,d),Q(next_state))
    view_exact=lib.assumption('view_change_exact',[['state',S],['change',D]],call(view_apply,qs,Delta(s,d)),Q(next_state))
    project_exact=lib.assumption('project_repair_exact',[['view',V],['view_change',E]],PR(P(v),v,e),P(call(view_apply,v,e)))
    lib.theorem('repair_composition',[['state',S],['change',D]],
        PR(P(qs),qs,Delta(s,d)),P(Q(next_state)),
        trans(use(project_exact,qs,Delta(s,d)),congruence(project,use(view_exact,s,d))))
    lib.theorem('repair_two_changes',[['state',S],['change',D],['next_change',D]],
        R(R(qs,s,d),next_state,d2),Q(A(next_state,d2)),
        trans(congruence(repair,use(exact,s,d),refl(next_state),refl(d2)),use(exact,next_state,d2)))
    # Repair composition through a pure downstream projection needs no derived
    # change language: this alternative re-evaluates the downstream projection.
    lib.theorem('project_after_repair',[['state',S],['change',D]],P(R(qs,s,d)),P(Q(next_state)),congruence(project,use(exact,s,d)))
    # Encode/decode and transition correspondence compose across representations.
    T,F=(lib.sort(n)for n in ('Physical','NextPhysical'))
    enc=lib.abstract('encode',[S],T);dec=lib.abstract('decode',[T],S)
    enc2=lib.abstract('encode_next',[T],F);dec2=lib.abstract('decode_next',[F],T)
    t=var('physical')
    roundtrip=lib.assumption('roundtrip',[['state',S]],call(dec,call(enc,s)),s)
    roundtrip2=lib.assumption('roundtrip_next',[['physical',T]],call(dec2,call(enc2,t)),t)
    lib.theorem('roundtrip_composition',[['state',S]],
        call(dec,call(dec2,call(enc2,call(enc,s)))),s,
        trans(congruence(dec,use(roundtrip2,call(enc,s))),use(roundtrip,s)))
    step=lib.abstract('physical_step',[T,D],T)
    step2=lib.abstract('next_physical_step',[F,D],F)
    correspondence=lib.assumption('step_correspondence',[['state',S],['change',D]],call(step,call(enc,s),d),call(enc,A(s,d)))
    correspondence2=lib.assumption('next_step_correspondence',[['physical',T],['change',D]],call(step2,call(enc2,t),d),call(enc2,call(step,t,d)))
    lib.theorem('step_correspondence_composition',[['state',S],['change',D]],
        call(step2,call(enc2,call(enc,s)),d),call(enc2,call(enc,A(s,d))),
        trans(use(correspondence2,call(enc,s),d),congruence(enc2,use(correspondence,s,d))))
    # A shared traversal preserves the exact order of each separate fold. No
    # commutativity/associativity assumption: suitable even for ordered folds.
    H,M,N=(lib.sort(n)for n in ('Element','LeftTotal','RightTotal'))
    left_zero=lib.abstract('left_zero',[],M);right_zero=lib.abstract('right_zero',[],N)
    left_step=lib.abstract('left_step',[M,H],M);right_step=lib.abstract('right_step',[N,H],N)
    pair=lib.store('Totals','Datatype',dict(constructors=[dict(name='Totals',fields=[M,N])]))
    L=lib.list_of('Rows',H);LS={'Data':L};PS={'Data':pair}
    xs,head,tail=map(var,('xs','head','tail'))
    fold_left=lib.function('fold_left',[['xs',LS]],M,match(xs,([],call(left_zero)),(['head','tail'],call(left_step,self_call(tail),head))),0)
    fold_right=lib.function('fold_right',[['xs',LS]],N,match(xs,([],call(right_zero)),(['head','tail'],call(right_step,self_call(tail),head))),0)
    pair_step=lib.function('pair_step',[['totals',PS],['head',H]],PS,
        match(var('totals'),(['left','right'],construct(pair,0,call(left_step,var('left'),head),call(right_step,var('right'),head)))))
    empty=construct(pair,0,call(left_zero),call(right_zero))
    shared=lib.function('fold_shared',[['xs',LS]],PS,match(xs,([],empty),(['head','tail'],call(pair_step,self_call(tail),head))),0)
    lhs=call(shared,xs);rhs=construct(pair,0,call(fold_left,xs),call(fold_right,xs))
    lib.theorem('shared_fold_exact',[['xs',LS]],lhs,rhs,induction('xs',lhs,rhs,refl(empty),congruence(pair_step,hyp(0),refl(head))))
    a,b=var('left_total'),var('right_total')
    lf=lib.function('fold_left_sequence',[['xs',LS],['left_total',M]],M,match(xs,([],a),(['head','tail'],self_call(tail,call(left_step,a,head)))),0)
    rf=lib.function('fold_right_sequence',[['xs',LS],['right_total',N]],N,match(xs,([],b),(['head','tail'],self_call(tail,call(right_step,b,head)))),0)
    sf=lib.function('fold_shared_sequence',[['xs',LS],['totals',PS]],PS,match(xs,([],var('totals')),(['head','tail'],self_call(tail,call(pair_step,var('totals'),head)))),0)
    lhs=call(sf,xs,construct(pair,0,a,b));rhs=construct(pair,0,call(lf,xs,a),call(rf,xs,b))
    lib.theorem('shared_left_fold_exact',[['xs',LS],['left_total',M],['right_total',N]],lhs,rhs,
        {'GeneralizedInduction':dict(variable='xs',generalize=['left_total','right_total'],**{'from':lhs,'to':rhs},cases=[dict(bindings=[],proof=refl(construct(pair,0,a,b))),dict(bindings=['head','tail'],proof={'GeneralizedHypothesis':dict(index=0,arguments=[call(left_step,a,head),call(right_step,b,head)])})])})
    keyed_tables(lib)
    from producers.top_k_laws import build as build_top_k
    build_top_k(lib)
    from producers.field_dependency_laws import build as build_fields
    build_fields(lib)
    from producers.indexed_state_laws import build as build_index
    build_index(lib)
    from producers.filtered_projection_laws import build as build_projection
    build_projection(lib)
    from producers.grouped_aggregate_laws import build as build_groups
    build_groups(lib)
    from producers.indexed_join_laws import build as build_join
    build_join(lib)
    return lib

def keyed_tables(lib):
    """Parameterized lookup repair and write coalescing on arbitrary row lists."""
    from producers.point_delta import normal,equality,binary,choice,replace,lift
    row=lib.sort('StateRow');rows=lib.store('WordRows','Datatype',dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',row,'SelfType'])]))
    option=lib.store('RowOption','Datatype',dict(constructors=[dict(name='None',fields=[]),dict(name='Some',fields=[row])]))
    RS={'Data':rows};OS={'Data':option}
    r,k,n=map(var,('rows','key','new'));h,x,t=map(var,('head','value','tail'))
    nil=construct(rows,0);none=construct(option,0);some=lambda x:construct(option,1,x)
    cons=lambda h,x,t:construct(rows,1,h,x,t)
    guard=binary('==',k,h)
    get=lib.function('get',[['rows',RS],['key','U64']],OS,match(r,([],none),(['head','value','tail'],choice(guard,some(x),self_call(t,k)))),0)
    remove=lib.function('remove',[['rows',RS],['key','U64']],RS,match(r,([],nil),(['head','value','tail'],choice(guard,self_call(t,k),cons(h,x,self_call(t,k))))),0)
    rep=lib.function('replace',[['rows',RS],['key','U64'],['new',row]],RS,match(r,([],nil),(['head','value','tail'],cons(h,choice(guard,n,x),self_call(t,k,n)))),0)
    contains=lib.function('contains',[['rows',RS],['key','U64']],'Bool',match(call(get,r,k),([],{'Bool':False}),(['value'],{'Bool':True})),extra=[option])
    present=lib.function('replace_present',[['old',OS],['new',row]],OS,match(var('old'),([],none),(['previous'],some(n))))
    G=lambda r:call(get,r,k);D=lambda r:call(remove,r,k);R=lambda r,n:call(rep,r,k,n)
    # point_delta's bounded authoring tactic creates only ordinary Convert,
    # Substitute, BoolSplit and induction nodes. The compiler replays all nodes.
    laws=[('contains_replace',lambda r:call(contains,R(r,n),k),lambda r:call(contains,r,k),[['new',row]]),
          ('lookup_remove',lambda r:G(D(r)),lambda r:none,[]),
          ('lookup_replace',lambda r:G(R(r,n)),lambda r:call(present,G(r),n),[['new',row]]),
          ('replace_overwrite',lambda r:R(R(r,var('old')),n),lambda r:R(r,n),[['old',row],['new',row]]),
          ('remove_after_replace',lambda r:D(R(r,n)),D,[['new',row]]),
          ('replace_after_remove',lambda r:R(D(r),n),D,[['new',row]])]
    h,x,t=map(var,('proof_key','proof_row','proof_tail'));guard=binary('==',k,h)
    bound=cons(h,x,t)
    for name,left,right,extras in laws:
        a,z=left(bound),right(bound);na,nz=normal(a,lib.objects),normal(z,lib.objects);branches={}
        for flag in (False,True):
            context_a=replace(na,guard,var('delta_hole'));context_z=replace(nz,guard,var('delta_hole'))
            ca=replace(na,guard,{'Bool':flag});cz=replace(nz,guard,{'Bool':flag})
            from producers.action_replacement import convert
            branches['on_true' if flag else 'on_false']=trans(convert(a,na),lift(hyp(1),context_a),equality(ca,cz,lib.objects,(left(t),right(t),0),[(guard,{'Bool':flag},1)]),sym(lift(hyp(1),context_z)),convert(nz,z))
        step={'BoolSplit':dict(condition=guard,**{'from':a,'to':z},**branches)}
        proof={'Induction':dict(variable='rows',**{'from':left(r),'to':right(r)},cases=[dict(bindings=[],proof=equality(left(nil),right(nil),lib.objects)),dict(bindings=['proof_key','proof_row','proof_tail'],proof=step)])}
        lib.theorem(name,[['rows',RS],['key','U64']]+extras,left(r),right(r),proof,[option] if name in ('contains_replace','lookup_replace') else [])
    key_locality(lib,rows,row,option,get,remove,rep)
    general_lookup_updates(lib,rows,row,option,get,remove,rep,present)
    key_commutation(lib,rows,row,remove,rep)
    sorted_rows(lib)

def sorted_rows(lib):
    """Insertion, strict sortedness, and laws that hold only on sorted rows
    (see producers/sorted_rows.py). Word facts use cached bit-blasting
    certificates; the checker replays every one."""
    from producers import sorted_rows as rows
    from producers.workspace import compiler_path
    cache=Path(__file__).resolve().parents[1]/'research/composable-state/sorted-row-certificates.json'
    certificates=json.loads(cache.read_text()) if cache.exists() else {}
    before=dict(certificates)
    rows.build(lib,compiler_path(),certificates)
    if certificates!=before:cache.write_text(json.dumps(certificates,sort_keys=True,separators=(',',':'))+'\n')

def key_commutation(lib,rows,row,remove,rep):
    """Updates of two keys commute: two removals always, and a removal with a
    replacement always (a replacement keeps keys; a removal filters by key).
    Both hold for any row list, sorted or not, and for equal keys too."""
    from producers.point_delta import binary,equality
    r,k,q,n=map(var,('rows','key','other','new'));h,x,t=map(var,('proof_key','proof_row','proof_tail'))
    RS={'Data':rows};nil=construct(rows,0);bound=construct(rows,1,h,x,t)
    D=lambda r,key:call(remove,r,key);R=lambda r,key,v:call(rep,r,key,v)
    laws=[('remove_remove_commute',lambda r:D(D(r,k),q),lambda r:D(D(r,q),k),[]),
          ('remove_replace_commute',lambda r:D(R(r,k,n),q),lambda r:R(D(r,q),k,n),[['new',row]])]
    first,second=binary('==',k,h),binary('==',q,h)
    for name,left,right,extras in laws:
        a,z=left(bound),right(bound)
        def leaf(fk,fq):
            return equality(a,z,lib.objects,(left(t),right(t),0),[(first,{'Bool':fk},1),(second,{'Bool':fq},2)])
        def inner(fk):
            return {'BoolSplit':dict(condition=second,**{'from':a,'to':z},on_true=leaf(fk,True),on_false=leaf(fk,False))}
        step={'BoolSplit':dict(condition=first,**{'from':a,'to':z},on_true=inner(True),on_false=inner(False))}
        proof={'Induction':dict(variable='rows',**{'from':left(r),'to':right(r)},cases=[dict(bindings=[],proof=equality(left(nil),right(nil),lib.objects)),dict(bindings=['proof_key','proof_row','proof_tail'],proof=step)])}
        lib.theorem(name,[['rows',RS],['key','U64'],['other','U64']]+extras,left(r),right(r),proof)

def general_lookup_updates(lib,rows,row,option,get,remove,rep,present):
    import subprocess,tempfile
    from producers.point_delta import binary,choice,equality,lift
    from producers.action_replacement import convert
    from producers.workspace import compiler_path
    q,k,r,n=map(var,('query','key','rows','new'));guard=binary('==',q,k)
    goal=dict(params=[['query','U64'],['key','U64']],conditions=[dict(**{'from':guard,'to':{'Bool':True}})],**{'from':q,'to':k})
    cache=Path(__file__).resolve().parents[1]/'research/composable-state/key-equality-certificate.json'
    if cache.exists():
        value=json.loads(cache.read_text())
        if value['goal']!=goal:raise ValueError('key reflection certificate goal mismatch')
        cert=value['certificate']
    else:
        from producers.bitvector_proofs import certificate
        with tempfile.TemporaryDirectory(prefix='ink-key-reflection-')as tmp:
            a=Path(tmp)/'goal.json';b=Path(tmp)/'cnf.json';a.write_text(json.dumps(goal))
            subprocess.run([str(compiler_path()),'bitvector-obligation',str(a),'-o',str(b)],check=True,capture_output=True)
            cert=certificate(json.loads(b.read_text()))
        cache.write_text(json.dumps(dict(goal=goal,certificate=cert),separators=(',',':'))+'\n')
    reflected=lib.store('word_equal_from_guard','Theorem',dict(**goal,proof={'BitVector':dict(**{'from':q,'to':k},hypotheses=[0],certificate=cert)}))
    equal={'Use':dict(theorem=reflected,arguments=[q,k],premises=[hyp(0)])}
    none=construct(option,0)
    for name,op,extra,args in [('remove',remove,[],[k]),('replace',rep,[['new',row]],[k,n])]:
        updated=call(op,r,*args);a=call(get,updated,q)
        same=none if name=='remove'else call(present,call(get,r,q),n)
        z=choice(guard,same,call(get,r,q))
        masked_a=choice(guard,none,a);masked_z=choice(guard,none,call(get,r,q))
        other=use(lib.names['lookup_'+name+'_other_key'],r,k,q,*([n]if name=='replace'else[]))
        no=trans(sym(equality(masked_a,a,lib.objects,facts=[(guard,{'Bool':False},0)])),other,equality(masked_z,z,lib.objects,facts=[(guard,{'Bool':False},0)]))
        yes=trans({'Substitute':dict(variable='key_hole',context=call(get,updated,var('key_hole')),equality=equal)},use(lib.names['lookup_'+name],r,k,*([n]if name=='replace'else[])))
        if name=='replace':yes=trans(yes,{'Sym':{'Substitute':dict(variable='key_hole',context=call(present,call(get,r,var('key_hole')),n),equality=equal)}})
        yes=trans(yes,equality(same,z,lib.objects,facts=[(guard,{'Bool':True},0)]))
        proof={'BoolSplit':dict(condition=guard,**{'from':a,'to':z},on_false=no,on_true=yes)}
        lib.theorem('lookup_general_'+name,[['rows',{'Data':rows}],['key','U64'],['query','U64']]+extra,a,z,proof,extra=[option])

def key_locality(lib,rows,row,option,get,remove,rep):
    import hashlib,subprocess,tempfile
    from producers.point_delta import binary,choice,equality
    from producers.workspace import compiler_path
    r,k,q,h,x,t=map(var,('rows','key','query','proof_key','proof_row','proof_tail'))
    qq,kk,hh=map(var,('q','k','h'))
    conditions=[dict(**{'from':binary('==',qq,kk),'to':{'Bool':False}}),dict(**{'from':binary('==',kk,hh),'to':{'Bool':True}})]
    goal=dict(params=[['q','U64'],['k','U64'],['h','U64']],conditions=conditions,**{'from':binary('==',qq,hh),'to':{'Bool':False}})
    cache=Path(__file__).resolve().parents[1]/'research/composable-state/key-disjoint-certificate.json'
    if cache.exists():
        proof=json.loads(cache.read_text())
        if proof['goal']!=goal:raise ValueError('key-disjoint certificate goal mismatch')
        cert=proof['certificate']
    else:
        from producers.bitvector_proofs import certificate
        with tempfile.TemporaryDirectory(prefix='ink-key-locality-')as temp:
            source=Path(temp)/'goal.json';cnf=Path(temp)/'cnf.json';source.write_text(json.dumps(goal))
            subprocess.run([str(compiler_path()),'bitvector-obligation',str(source),'-o',str(cnf)],check=True,capture_output=True)
            cert=certificate(json.loads(cnf.read_text()))
        cache.parent.mkdir(parents=True,exist_ok=True);cache.write_text(json.dumps(dict(goal=goal,certificate=cert),separators=(',',':'))+'\n')
    disjoint=lib.store('distinct_keys_do_not_match_same_head','Theorem',dict(**goal,proof={'BitVector':dict(**{k:goal[k]for k in ('from','to')},hypotheses=[0,1],certificate=cert)}))
    none=construct(option,0);nil=construct(rows,0);bound=construct(rows,1,h,x,t)
    guard=binary('==',q,k);head_guard=binary('==',k,h)
    G=lambda r:call(get,r,q)
    for name,update,extras in [('lookup_remove_other_key',lambda r:call(remove,r,k),[]),('lookup_replace_other_key',lambda r:call(rep,r,k,var('new')),[['new',row]])]:
        left=lambda r:choice(guard,none,G(update(r)));right=lambda r:choice(guard,none,G(r))
        branches={}
        for flag in (False,True):
            facts=[(guard,{'Bool':False},1),(head_guard,{'Bool':flag},2)]
            if flag:facts.append((binary('==',q,h),{'Bool':False},{'Use':dict(theorem=disjoint,arguments=[q,k,h],premises=[hyp(1),hyp(2)])}))
            branches['on_true'if flag else 'on_false']=equality(left(bound),right(bound),lib.objects,(left(t),right(t),0),facts)
        no={'BoolSplit':dict(condition=head_guard,**{'from':left(bound),'to':right(bound)},**branches)}
        yes=equality(left(bound),right(bound),lib.objects,facts=[(guard,{'Bool':True},1)])
        step={'BoolSplit':dict(condition=guard,**{'from':left(bound),'to':right(bound)},on_false=no,on_true=yes)}
        proof={'Induction':dict(variable='rows',**{'from':left(r),'to':right(r)},cases=[dict(bindings=[],proof=equality(left(nil),right(nil),lib.objects)),dict(bindings=['proof_key','proof_row','proof_tail'],proof=step)])}
        lib.theorem(name,[['rows',{'Data':rows}],['key','U64'],['query','U64']]+extras,left(r),right(r),proof)

def publish(root,compiler,report):
    import hashlib,subprocess,tempfile
    root=Path(root).resolve();compiler=Path(compiler).resolve()
    compiler_hash=hashlib.sha256(compiler.read_bytes()).hexdigest()
    original=Store(root);old_ids=set(original.members());names=json.loads((original.data/'names.json').read_text())
    lib=build(CanonicalLibrary());objects=[original.object(i)for i in sorted(old_ids)]+list(lib.objects.values())
    names.update({'state-calculus/'+n:i for n,i in lib.names.items()})
    with tempfile.TemporaryDirectory(prefix='ink-state-admission-')as temp:
        stage=Path(temp);source=stage/'subject.ink';core=stage/'subject.json';view=stage/'view.json'
        source.write_text('module state_admission;fn identity(x:u32)->u32{return x;}')
        subprocess.run([str(compiler),'emit-core',str(source),'-o',str(core)],check=True,capture_output=True)
        checked=Store.publish(stage,objects,names);view.write_text(json.dumps(checked.bundle(sorted(lib.objects))))
        result=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],check=True,capture_output=True,text=True)
        if hashlib.sha256(compiler.read_bytes()).hexdigest()!=compiler_hash:raise RuntimeError('compiler changed during admission')
        published=Store.publish(root,objects,names)
        if published.snapshot_id!=checked.snapshot_id:raise RuntimeError('published snapshot differs from checked snapshot')
        published.rebuild()
    previous=Store(root,root/'store/snapshots'/f'{original.snapshot_id}.json')
    if set(previous.members())!=old_ids:raise RuntimeError('previous snapshot was not preserved')
    receipt=dict(schema=1,status='checked',previous_snapshot=original.snapshot_id,snapshot=published.snapshot_id,
        added_entries=len(set(lib.objects)-old_ids),compiler_sha256=compiler_hash,
        admission=json.loads(result.stdout),scope='Parametric equality. Concrete instances discharge assumptions; source action observations and physical eligibility remain separate obligations.')
    Path(report).parent.mkdir(parents=True,exist_ok=True);Path(report).write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory',type=Path);p.add_argument('--view',type=Path);p.add_argument('--publish',action='store_true');p.add_argument('--compiler',type=Path);p.add_argument('--report',type=Path)
    a=p.parse_args()
    if a.publish:
        if not a.compiler or not a.report:p.error('--publish requires --compiler and --report')
        receipt=publish(a.directory,a.compiler,a.report);print(json.dumps({k:v for k,v in receipt.items()if k!='admission'}));return
    lib=build(CanonicalLibrary());store=Store.publish(a.directory,lib.objects.values(),lib.names)
    if a.view:a.view.write_text(json.dumps(store.bundle(sorted(lib.objects)),separators=(',',':'))+'\n')
    print(json.dumps(dict(entries=len(lib.objects),snapshot=store.snapshot_id,status='proposed',authority='requires mathematical admission')))
if __name__=='__main__':main()
