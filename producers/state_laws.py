#!/usr/bin/env python3
"""Database-owned field frame laws and ordered grouped table traversals.

Untrusted authoring. The first-order kernel checks every theorem, including
arbitrary rows, duplicate keys and both intermediate and final values.
"""
import argparse,copy,json,subprocess,sys,tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from ink_knowledge import Store,identity,canonical
from ink_knowledge.store import entry
from action_replacement import var,call,cons,convert,trans
from representations import refs,match
from point_delta import normal

def replace(t,a,z):
    if t==a:return copy.deepcopy(z)
    if isinstance(t,dict):return {k:replace(v,a,z) for k,v in t.items()}
    if isinstance(t,list):return [replace(v,a,z) for v in t]
    return t

def derive(a,z,objects,hypotheses=(),budget=64,leaf=None,rules=()):
    if budget<=0:raise ValueError('proof authoring budget')
    n=lambda x:normal(x,objects)
    aa,zz=n(a),n(z)
    if aa==zz:return convert(a,z)
    for i,(x,y) in enumerate(hypotheses):
        x,y=n(x),n(y)
        changed=replace(aa,x,var('hole'))
        if changed!=aa:
            p={'Substitute':dict(variable='hole',context=changed,equality={'Hypothesis':i})}
            next=replace(aa,x,y)
            return trans(convert(a,aa),p,derive(next,z,objects,hypotheses,budget-1,leaf,rules))
    for x,y,p in rules:
        x,y=n(x),n(y)
        for current,on_left in [(aa,True),(zz,False)]:
            updated=replace(current,x,y)
            if updated!=current:
                lifted={'Substitute':dict(variable='rule_hole',context=replace(current,x,var('rule_hole')),equality=p)}
                if on_left:return trans(convert(a,aa),lifted,derive(updated,z,objects,hypotheses,budget-1,leaf,rules))
                return trans(derive(a,updated,objects,hypotheses,budget-1,leaf,rules),{'Sym':lifted},convert(zz,z))
    def condition(t):
        if isinstance(t,dict):
            if 'If'in t:return t['If']['condition']
            if 'Match'in t:return condition(t['Match']['scrutinee'])
            for v in t.values():
                found=condition(v)
                if found is not None:return found
        if isinstance(t,list):
            for v in t:
                found=condition(v)
                if found is not None:return found
        return None
    guard=condition(aa) or condition(zz)
    if guard is None and leaf is not None:return trans(convert(a,aa),leaf(aa,zz),convert(zz,z))
    if guard is None:raise ValueError('Cannot derive '+json.dumps([aa,zz])[:1500])
    branches={}
    for key,b in [('on_false',False),('on_true',True)]:
        fact=(guard,{'Bool':b});hole=var('decision')
        left=replace(aa,guard,hole);right=replace(zz,guard,hole)
        first={'Substitute':dict(variable='decision',context=left,equality={'Hypothesis':len(hypotheses)})}
        last={'Sym':{'Substitute':dict(variable='decision',context=right,equality={'Hypothesis':len(hypotheses)})}}
        chosen_a=replace(aa,guard,{'Bool':b});chosen_z=replace(zz,guard,{'Bool':b})
        branches[key]=trans(convert(a,aa),first,derive(chosen_a,chosen_z,objects,(*hypotheses,fact),budget-1,leaf,rules),last,convert(zz,z))
    return {'BoolSplit':dict(condition=guard,**{'from':a,'to':z},**branches)}

def library():
    objects={};names={}
    def add(name,decl):
        body=next(iter(decl.values()));obj=entry('theorem' if 'Theorem'in decl else 'definition','first-order-inductive-equality-v1',{'declaration':decl},refs(decl),parameters=dict(body.get('params',[])),result=body.get('result'),conditions=body.get('conditions',[]))
        i=identity(obj);objects[i]=obj;names[name]=i;return i
    def function(name,params,result,body,recursive=None):return add(name,{'Function':dict(params=params,result=result,body=body,recursive=recursive)})
    def theorem(name,params,a,z,proof):return add(name,{'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=proof)})
    row=add('Row',{'AbstractSort':{'name':'FrameRow'}});R={'Data':row}
    payload=add('Payload',{'AbstractSort':{'name':'FramePayload'}});V={'Data':payload}
    derived=add('Derived',{'AbstractSort':{'name':'FrameDerived'}});D={'Data':derived}
    pair=add('Product',{'Datatype':dict(constructors=[dict(name='Product',fields=[R,V])])});P={'Data':pair};pv=lambda a,b:cons(pair,0,[a,b])
    first=function('read_left',[['p',P]],R,match(var('p'),[(['left','right'],var('left'))]))
    second=function('read_right',[['p',P]],V,match(var('p'),[(['left','right'],var('right'))]))
    setleft=function('write_left',[['p',P],['value',R]],P,match(var('p'),[(['left','right'],pv(var('value'),var('right')))]))
    setright=function('write_right',[['p',P],['value',V]],P,match(var('p'),[(['left','right'],pv(var('left'),var('value')))]))
    view=add('dependent_view',{'AbstractFunction':dict(name='ReadOnlyRightView',params=[['x',V]],result=D)})
    for name,a,z,rest in [
        ('read_right_after_left_write',call(second,[call(setleft,[var('p'),var('new_left')])]),call(second,[var('p')]),[['new_left',R]]),
        ('read_left_after_right_write',call(first,[call(setright,[var('p'),var('new_right')])]),call(first,[var('p')]),[['new_right',V]]),
        ('preserve_derived_right',call(view,[call(second,[call(setleft,[var('p'),var('new_left')])])]),call(view,[call(second,[var('p')])]),[['new_left',R]]),
        ('disjoint_writes_commute',call(setleft,[call(setright,[var('p'),var('new_right')]),var('new_left')]),call(setright,[call(setleft,[var('p'),var('new_left')]),var('new_right')]),[['new_left',R],['new_right',V]])]:
        bound=pv(var('left'),var('right'))
        proof={'Induction':dict(variable='p',**{'from':a,'to':z},cases=[dict(bindings=['left','right'],proof=convert(replace(a,var('p'),bound),replace(z,var('p'),bound)))])}
        theorem(name,[['p',P],*rest],a,z,proof)
    rows=add('Rows',{'Datatype':dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',R,'SelfType'])])});T={'Data':rows}
    transforms=[add(name,{'AbstractFunction':dict(name=name,params=[['row',R]],result=R)}) for name in ['first_edit','second_edit']]
    nil=cons(rows,0,[]);guard={'Binary':dict(op='==',left=var('key'),right=var('head'))}
    updates=[]
    for label,f in zip(['update_first','update_second'],transforms):
        tail={'SelfCall':[var('tail'),var('key')]}
        changed={'If':dict(condition=guard,on_true=call(f,[var('value')]),on_false=var('value'))}
        updates.append(function(label,[['rows',T],['key','U64']],T,match(var('rows'),[([],nil),(['head','value','tail'],cons(rows,1,[var('head'),changed,tail]))]),0))
    pairrows=add('IntermediateAndFinal',{'Datatype':dict(constructors=[dict(name='IntermediateAndFinal',fields=[T,T])])});B={'Data':pairrows};pair=lambda a,b:cons(pairrows,0,[a,b])
    firstrow={'If':dict(condition=guard,on_true=call(transforms[0],[var('value')]),on_false=var('value'))}
    lastrow={'If':dict(condition=guard,on_true=call(transforms[1],[firstrow]),on_false=var('value'))}
    joined=match({'SelfCall':[var('tail'),var('key')]},[(['first_tail','last_tail'],pair(cons(rows,1,[var('head'),firstrow,var('first_tail')]),cons(rows,1,[var('head'),lastrow,var('last_tail')])) )])
    batch=function('grouped_edits',[['rows',T],['key','U64']],B,match(var('rows'),[([],pair(nil,nil)),(['head','value','tail'],joined)]),0)
    first=lambda t:call(updates[0],[t,var('key')]);last=lambda t:call(updates[1],[first(t),var('key')]);a=call(batch,[var('rows'),var('key')]);z=pair(first(var('rows')),last(var('rows')))
    bound=cons(rows,1,[var('head'),var('value'),var('tail')]);hyp=[(call(batch,[var('tail'),var('key')]),pair(first(var('tail')),last(var('tail'))))]
    proof={'Induction':dict(variable='rows',**{'from':a,'to':z},cases=[dict(bindings=[],proof=convert(replace(a,var('rows'),nil),replace(z,var('rows'),nil))),dict(bindings=['head','value','tail'],proof=derive(replace(a,var('rows'),bound),replace(z,var('rows'),bound),objects,hyp))])}
    theorem('grouped_preserves_intermediate_and_final',[['rows',T],['key','U64']],a,z,proof)
    return objects,names

def publish(root,compiler,report):
    root=Path(root);compiler=Path(compiler).resolve();old=Store(root);objects,names=library();existing=json.loads((root/'store/names.json').read_text());existing.update({'state-laws/'+k:v for k,v in names.items()})
    allobjects=[old.object(i) for i in old.members()]+list(objects.values())
    with tempfile.TemporaryDirectory(prefix='ink-state-laws-') as tmp:
        d=Path(tmp);source=d/'source.ink';core=d/'core.json';view=d/'view.json';source.write_text('module state_laws; pub fn identity(x: u64) -> u64 { return x; }\n')
        subprocess.run([str(compiler),'emit-core',str(source),'-o',str(core)],check=True,capture_output=True)
        staged=Store.publish(d/'knowledge',allobjects,existing);view.write_bytes(canonical(staged.bundle(list(objects)))+b'\n')
        checked=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],capture_output=True,text=True)
        if checked.returncode:raise ValueError(checked.stderr)
        admitted=Store.publish(root,allobjects,existing);admitted.rebuild()
    receipt=dict(status='checked',previous_snapshot=old.snapshot_id,snapshot=admitted.snapshot_id,entries=names,admission=json.loads(checked.stdout))
    Path(report).parent.mkdir(parents=True,exist_ok=True);Path(report).write_text(json.dumps(receipt,indent=2)+'\n');return receipt
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--compiler',required=True);p.add_argument('--report',required=True);a=p.parse_args();print(json.dumps(publish(a.root,a.compiler,a.report)))
