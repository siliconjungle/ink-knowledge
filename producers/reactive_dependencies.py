#!/usr/bin/env python3
"""Untrusted dependency-factorisation and equal-output propagation laws.

A tracked-read list or observed sample is never a proof premise. Concrete
interpretations must prove that the specified dependencies determine the
observation, and discharge exact equality conditions.
"""
import argparse, hashlib, json, subprocess, sys, tempfile
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store
from producers.state_calculus import CanonicalLibrary
from producers.general_laws import var, call, refl, hyp, sym, use, trans, congruence
from producers.point_delta import choice


def build(lib):
    state=lib.sort('ReactiveState');dependencies=lib.sort('DependencySnapshot')
    value=lib.sort('ReactiveValue');result=lib.sort('DownstreamValue')
    read=lib.abstract('read_dependencies',[state],dependencies)
    compute=lib.abstract('compute_dependencies',[dependencies],value)
    observe=lib.abstract('observe_reactive_state',[state],value)
    project=lib.abstract('project_reactive_value',[value],result)
    s=var('state');previous=var('previous');following=var('following')
    factors=lib.assumption('dependencies_determine_observation',[['state',state]],call(observe,s),call(compute,call(read,s)))
    def law(name,params,conditions,left,right,proof):
        return lib.store(name,'Theorem',dict(params=params,conditions=conditions,**{'from':left,'to':right},proof=proof))
    law('observation_reuse_from_equal_dependencies',
        [['previous',state],['following',state]],
        [{'from':call(read,previous),'to':call(read,following)}],
        call(observe,previous),call(observe,following),
        trans(use(factors,previous),congruence(compute,hyp(0)),sym(use(factors,following))))
    before=var('before');after=var('after')
    law('downstream_reuse_from_equal_values',[['before',value],['after',value]],
        [{'from':before,'to':after}],call(project,before),call(project,after),congruence(project,hyp(0)))
    left_read=lib.abstract('read_left_dependencies',[state],dependencies)
    right_read=lib.abstract('read_right_dependencies',[state],dependencies)
    left_compute=lib.abstract('compute_left_dependencies',[dependencies],value)
    right_compute=lib.abstract('compute_right_dependencies',[dependencies],value)
    flag=var('flag');dep=var('dependencies')
    selected=lib.function('active_branch_dependencies',[['flag','Bool'],['state',state]],dependencies,
        choice(flag,call(left_read,s),call(right_read,s)))
    evaluate=lib.function('active_branch_compute',[['flag','Bool'],['dependencies',dependencies]],value,
        choice(flag,call(left_compute,dep),call(right_compute,dep)))
    observed=lib.function('active_branch_observation',[['flag','Bool'],['state',state]],value,
        call(evaluate,flag,call(selected,flag,s)))
    f0=var('previous_flag');f1=var('following_flag')
    a=call(observed,f0,previous);z=call(observed,f1,following)
    expanded_a=call(evaluate,f0,call(selected,f0,previous))
    expanded_z=call(evaluate,f1,call(selected,f1,following))
    law('active_branch_reuse',[['previous_flag','Bool'],['following_flag','Bool'],['previous',state],['following',state]],
        [{'from':f0,'to':f1},{'from':call(selected,f0,previous),'to':call(selected,f1,following)}],a,z,
        trans({'Convert':{'from':a,'to':expanded_a}},congruence(evaluate,hyp(0),hyp(1)),{'Convert':{'from':expanded_z,'to':z}}))
    return lib


def publish(root,compiler,report):
    root=Path(root).resolve();compiler=Path(compiler).resolve()
    old=Store(root);old_ids=set(old.members());lib=build(CanonicalLibrary())
    objects=[old.object(i) for i in sorted(old_ids)]+list(lib.objects.values())
    names=json.loads((old.data/'names.json').read_text())
    names.update({'reactive-dependencies/'+name:i for name,i in lib.names.items()})
    compiler_hash=hashlib.sha256(compiler.read_bytes()).hexdigest()
    with tempfile.TemporaryDirectory(prefix='ink-reactive-laws-') as temporary:
        stage=Path(temporary);source=stage/'subject.ink';core=stage/'subject.json';view=stage/'view.json'
        source.write_text('module reactive_admission;fn identity(x:u32)->u32{return x;}')
        subprocess.run([str(compiler),'emit-core',str(source),'-o',str(core)],check=True,capture_output=True)
        checked=Store.publish(stage,objects,names)
        view.write_text(json.dumps(checked.bundle(sorted(lib.objects))))
        verdict=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],check=True,capture_output=True,text=True)
        if hashlib.sha256(compiler.read_bytes()).hexdigest()!=compiler_hash:raise RuntimeError('compiler changed during admission')
        published=Store.publish(root,objects,names)
        if published.snapshot_id!=checked.snapshot_id:raise RuntimeError('publication differs from checked snapshot')
        published.rebuild()
    if set(Store(root,root/'store/snapshots'/f'{old.snapshot_id}.json').members())!=old_ids:raise RuntimeError('old snapshot changed')
    receipt=dict(schema=1,status='checked',previous_snapshot=old.snapshot_id,snapshot=published.snapshot_id,
        added_entries=len(set(lib.objects)-old_ids),compiler_sha256=compiler_hash,admission=json.loads(verdict.stdout),
        scope='Parametric dependency factorisation, branch-scoped reuse and equal-output propagation. Concrete source interpretations must discharge assumptions and equality premises. No measured read trace, cache name, profile or scheduler grants authority.')
    Path(report).parent.mkdir(parents=True,exist_ok=True);Path(report).write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directory',type=Path);p.add_argument('--view',type=Path)
    p.add_argument('--publish',action='store_true');p.add_argument('--compiler',type=Path);p.add_argument('--report',type=Path);a=p.parse_args()
    if a.publish:
        if not a.compiler or not a.report:p.error('--publish requires --compiler and --report')
        print(json.dumps(publish(a.directory,a.compiler,a.report)));sys.exit(0)
    lib=build(CanonicalLibrary());store=Store.publish(a.directory,lib.objects.values(),lib.names)
    if a.view:a.view.write_text(json.dumps(store.bundle(sorted(lib.objects)),separators=(',',':'))+'\n')
    print(json.dumps(dict(status='proposed',entries=len(lib.objects),snapshot=store.snapshot_id)))
