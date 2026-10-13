#!/usr/bin/env python3
"""Untrusted whole-action equality proposal over checked source projections.

Individual definitions/theorems go into a content-addressed database snapshot.
This initial producer proposes remove idempotence; the compiler knows neither
that rule nor this producer and rechecks the complete transition equations.
"""
import argparse,copy,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,identity
from ink_knowledge.store import entry,read
MATH='first-order-inductive-equality-v1'
def var(n):return {'Var':n}
def call(f,xs):return {'Call':dict(function=f,arguments=xs)}
def cons(d,i,xs):return {'Construct':dict(datatype=d,constructor=i,arguments=xs)}
def convert(a,b):return {'Convert':{'from':a,'to':b}}
def trans(*proofs):
    out=proofs[0]
    for p in proofs[1:]:out={'Trans':[out,p]}
    return out

def theorem(table):
    d=table['datatype'];remove=table['remove'];row_sort=table['value_sort']
    rem=lambda rows:call(remove,[rows,var('key')])
    lhs=lambda rows:rem(rem(rows))
    nil=cons(d,0,[]);tail=var('tail');head=cons(d,1,[var('head'),var('value'),tail])
    ih_a,ih_z=lhs(tail),rem(tail)
    head_a,head_z=lhs(head),rem(head)
    ctor_a=cons(d,1,[var('head'),var('value'),ih_a]);ctor_z=cons(d,1,[var('head'),var('value'),ih_z])
    guard={'Binary':dict(op='==',left=var('key'),right=var('head'))}
    def conditional(flag,a,z):return {'If':dict(condition=flag,on_true=a,on_false=z)}
    def rhead(flag):return conditional(flag,ih_z,cons(d,1,[var('head'),var('value'),ih_z]))
    def rewrite(context):return {'Substitute':dict(variable='decision',context=context,equality={'Hypothesis':1})}
    left_context=rem(rhead(var('decision')))
    right_context=rhead(var('decision'))
    first=rewrite(left_context)
    last={'Sym':rewrite(right_context)}
    true_case=trans(convert(head_a,rem(rhead(guard))),first,{'Hypothesis':0},last,convert(rhead(guard),head_z))
    second=rewrite(conditional(var('decision'),ih_a,ctor_a))
    middle={'Construct':dict(datatype=d,constructor=1,arguments=[{'Refl':var('head')},{'Refl':var('value')},{'Hypothesis':0}])}
    false_case=trans(convert(head_a,rem(rhead(guard))),first,second,middle,last,convert(rhead(guard),head_z))
    case={'BoolSplit':dict(condition=guard,**{'from':head_a,'to':head_z},on_true=true_case,on_false=false_case)}
    declaration={'Theorem':dict(params=[['rows',{'Data':d}],['key','U64']],conditions=[],
        **{'from':lhs(var('rows')),'to':rem(var('rows'))},
        proof={'Induction':dict(variable='rows',**{'from':lhs(var('rows')),'to':rem(var('rows'))},cases=[dict(bindings=[],proof=convert(lhs(nil),rem(nil))),dict(bindings=['head','value','tail'],proof=case)])})}
    return entry('theorem',MATH,{'declaration':declaration},[d,remove,row_sort] if isinstance(row_sort,str) else [d,remove],parameters=dict(declaration['Theorem']['params']))

def general_law():
    """Stable entries, proved once over an abstract row sort. No program induction."""
    row=entry('definition',MATH,{'declaration':{'AbstractSort':dict(name='StateRow')}})
    element=identity(row)
    rows=entry('definition',MATH,{'declaration':{'Datatype':dict(constructors=[dict(name='Nil',fields=[]),dict(name='Cons',fields=['U64',{'Data':element},'SelfType'])])}},[element])
    datatype=identity(rows)
    recursive={'SelfCall':[var('tail'),var('key')]}
    body={'Match':dict(scrutinee=var('rows'),branches=[dict(bindings=[],body=cons(datatype,0,[])),dict(bindings=['head','value','tail'],body={'If':dict(condition={'Binary':dict(op='==',left=var('key'),right=var('head'))},on_true=recursive,on_false=cons(datatype,1,[var('head'),var('value'),recursive]))})])}
    remove=entry('definition',MATH,{'declaration':{'Function':dict(params=[['rows',{'Data':datatype}],['key','U64']],result={'Data':datatype},body=body,recursive=0)}},[element,datatype],parameters={'rows':{'Data':datatype},'key':'U64'},result={'Data':datatype})
    function=identity(remove)
    law=theorem(dict(datatype=datatype,remove=function,value_sort=element))
    objects={identity(x):x for x in [row,rows,remove,law]}
    return objects,dict(StateRow=element,WordRows=datatype,remove=function,remove_idempotence=identity(law))

def alpha_normal(t,depth=0,env=None):
    """Producer alpha normal form; every conversion is separately replayed."""
    env=env or {}
    if isinstance(t,list):return [alpha_normal(x,depth,env)for x in t]
    if not isinstance(t,dict):return t
    if set(t)=={'Var'}:return var(env.get(t['Var'],t['Var']))
    if 'Match'in t:
        node=t['Match'];branches=[]
        for branch in node['branches']:
            names=[f'__action_alpha_{depth+i}'for i in range(len(branch['bindings']))]
            local={**env,**dict(zip(branch['bindings'],names))}
            branches.append(dict(bindings=names,body=alpha_normal(branch['body'],depth+len(names),local)))
        return {'Match':dict(scrutinee=alpha_normal(node['scrutinee'],depth,env),branches=branches)}
    return {k:alpha_normal(v,depth,env)for k,v in t.items()}

def guarded_equality(a,z,objects,index=0,depth=0):
    """Bounded branch proof, including runtime presence/error checks."""
    from producers.point_delta import normal,replace,lift
    a0,z0=alpha_normal(normal(a,objects)),alpha_normal(normal(z,objects))
    if a0==z0:return convert(a,z)
    if depth>=12:return convert(a,z) # kernel rejection is the fallback
    conditional=a0.get('If',z0.get('If'))
    if conditional is None:return convert(a,z)
    guard=conditional['condition'];hole=var('delta_hole')
    ca,cz=replace(a0,guard,hole),replace(z0,guard,hole)
    branches={}
    for flag in (False,True):
        na=replace(a0,guard,{'Bool':flag});nz=replace(z0,guard,{'Bool':flag})
        h={'Hypothesis':index}
        branches['on_true'if flag else 'on_false']=trans(convert(a,a0),lift(h,ca),guarded_equality(na,nz,objects,index+1,depth+1),{'Sym':lift(h,cz)},convert(z0,z))
    return {'BoolSplit':dict(condition=guard,**{'from':a,'to':z},**branches)}

def produce(before,after,selected,directory,knowledge_root=None,snapshot=None):
    if before['semantics']!='ink-action-transition-v1' or after['semantics']!=before['semantics']:raise ValueError('incompatible projection')
    if before['state']!=after['state'] or before['events']!=after['events']:raise ValueError('transition representation changed')
    objects={**before['objects'],**after['objects']};proofs={};laws={}
    database=Store(Path(knowledge_root) if knowledge_root else Path(__file__).resolve().parents[1],snapshot)
    names=read(database.data/'names.json')
    roles={n:names['action-laws/'+n] for n in ['StateRow','WordRows','remove','remove_idempotence']}
    # Retrieve pinned database bytes. Authoring the four-entry induction library
    # is a separate command; proposals instantiate it rather than regenerate it.
    extra_names=['StateRow','WordRows','remove','replace','get','RowOption','contains','contains_replace','replace_overwrite','remove_after_replace','replace_after_remove']
    extra={n:names['state-calculus/'+n] for n in extra_names} if all('state-calculus/'+n in names for n in extra_names) else {}
    general=database.bundle(sorted(set(roles.values())|set(extra.values())))['objects'];objects.update(general)
    coalescing=[]
    for t in before['tables']:
        ty=json.dumps(t['value_type'],sort_keys=True,separators=(',',':'));sort=before['types'][ty]
        laws[t['remove']]=dict(theorem=roles['remove_idempotence'],sorts={roles['StateRow']:sort},functions={},
            definitions={roles['WordRows']:t['datatype'],roles['remove']:t['remove']},assumptions={})
        for rule in (['replace_overwrite','remove_after_replace','replace_after_remove','contains_replace'] if extra else []):
            law=dict(theorem=extra[rule],sorts={extra['StateRow']:sort},functions={},
                definitions={extra['WordRows']:t['datatype'],extra['remove']:t['remove'],extra['replace']:t['replace']},assumptions={})
            # Exactly the definitions used by this theorem are required; extra
            # remove for overwrite is harmless but creates an unnecessary edge.
            if rule in ('replace_overwrite','contains_replace'):law['definitions'].pop(extra['remove'])
            if rule=='contains_replace':
                law['definitions'][extra['get']]=t['get'];law['definitions'][extra['contains']]=t['contains']
                option=objects[t['get']]['payload']['declaration']['Function']['result']['Data']
                law['definitions'][names['state-calculus/RowOption']]=option
            coalescing.append((t,rule,law))
    # Two-key commutation (state-calculus/key_commutation): both sides are put
    # in one canonical order, removals innermost and in key order. Each step is
    # an instance the compiler replays; the order is only a search convention.
    commuting=[]
    if all('state-calculus/'+n in names for n in ('remove_remove_commute','remove_replace_commute')):
        for t in before['tables']:
            ty=json.dumps(t['value_type'],sort_keys=True,separators=(',',':'));sort=before['types'][ty]
            rows_role,remove_role,replace_role=names['state-calculus/WordRows'],names['state-calculus/remove'],names['state-calculus/replace']
            for rule in ('remove_remove_commute','remove_replace_commute'):
                definitions={rows_role:t['datatype'],remove_role:t['remove']}
                if rule=='remove_replace_commute':definitions[replace_role]=t['replace']
                law=dict(theorem=names['state-calculus/'+rule],sorts={names['state-calculus/StateRow']:sort},functions={},definitions=definitions,assumptions={})
                general.update(database.bundle([law['theorem']])['objects'])
                commuting.append((t,rule,law))
    objects.update(general)
    used_commuting=set()
    def canonical(term):
        def find(t):
            if isinstance(t,dict) and 'Call' in t:
                outer=t['Call'];args=outer['arguments']
                if len(args)==2 and isinstance(args[0],dict) and 'Call' in args[0]:
                    inner=args[0]['Call'];inside=inner['arguments']
                    for table,rule,law in commuting:
                        if outer['function']!=table['remove']:continue
                        if rule=='remove_remove_commute' and inner['function']==table['remove'] and len(inside)==2:
                            if json.dumps(args[1],sort_keys=True)<json.dumps(inside[1],sort_keys=True):
                                return t,call(table['remove'],[call(table['remove'],[inside[0],args[1]]),inside[1]]),law,[inside[0],inside[1],args[1]]
                        if rule=='remove_replace_commute' and inner['function']==table['replace'] and len(inside)==3:
                            return t,call(table['replace'],[call(table['remove'],[inside[0],args[1]]),inside[1],inside[2]]),law,[inside[0],inside[1],args[1],inside[2]]
            if isinstance(t,dict):
                for k in sorted(t):
                    r=find(t[k])
                    if r:return r
            if isinstance(t,list):
                for x in t:
                    r=find(x)
                    if r:return r
            return None
        def swap(t,target,value):
            if t==target:return copy.deepcopy(value)
            if isinstance(t,dict):return {k:swap(v,target,value) for k,v in t.items()}
            if isinstance(t,list):return [swap(v,target,value) for v in t]
            return t
        steps=[];current=copy.deepcopy(term)
        for _ in range(64):
            found=find(current)
            if not found:break
            original,replacement,law,args=found
            context=swap(current,original,var('replacement_rows'))
            steps.append({'Substitute':dict(variable='replacement_rows',context=context,equality={'Instance':dict(**law,arguments=args,premises=[])})})
            used_commuting.add(law['theorem'])
            current=swap(current,original,replacement)
        return current,steps
    for name,a in before['actions'].items():
        z=after['actions'][name];old=a['case']['call'];new=z['case']['call']
        if a['function']==z['function']:
            proofs[name]={'Refl':call(a['function'],[var(n) for n,_ in a['params']])};continue
        start=a['case']['normal'];end=z['case']['normal'];current=copy.deepcopy(start);steps=[]
        # Bounded deterministic traversal. Equality is lifted through its exact
        # surrounding term; intervening reads/events cannot be silently dropped.
        def find(t):
            if isinstance(t,dict) and 'Call' in t:
                f=t['Call']['function'];args=t['Call']['arguments']
                if f in laws and len(args)==2 and isinstance(args[0],dict) and args[0].get('Call',{}).get('function')==f:
                    inner=args[0]['Call']['arguments']
                    if len(inner)==2 and inner[1]==args[1]:return t,call(f,[inner[0],args[1]]),laws[f],[inner[0],args[1]]
            if isinstance(t,dict) and 'Call' in t:
                outer=t['Call'];args=outer['arguments']
                if len(args)in (2,3) and isinstance(args[0],dict) and 'Call'in args[0]:
                    inner=args[0]['Call'];inside=inner['arguments']
                    if len(inside)in (2,3) and args[1]==inside[1]:
                        for table,rule,law in coalescing:
                            if rule=='replace_overwrite' and outer['function']==inner['function']==table['replace'] and len(args)==len(inside)==3:
                                return t,call(table['replace'],[inside[0],args[1],args[2]]),law,[inside[0],args[1],inside[2],args[2]]
                            if rule=='remove_after_replace' and outer['function']==table['remove'] and inner['function']==table['replace'] and len(args)==2 and len(inside)==3:
                                return t,call(table['remove'],[inside[0],args[1]]),law,[inside[0],args[1],inside[2]]
                            if rule=='replace_after_remove' and outer['function']==table['replace'] and inner['function']==table['remove'] and len(args)==3 and len(inside)==2:
                                return t,call(table['remove'],[inside[0],args[1]]),law,[inside[0],args[1],args[2]]
            if isinstance(t,dict) and 'Match'in t:
                node=t['Match'];get=node['scrutinee'].get('Call',{})
                ga=get.get('arguments',[]);branches=node['branches']
                if len(ga)==2 and 'Call'in ga[0] and len(branches)==2 and branches[0]['body']=={'Bool':False} and branches[1]['body']=={'Bool':True}:
                    update=ga[0]['Call'];ua=update['arguments']
                    for table,rule,law in coalescing:
                        if rule=='contains_replace' and get['function']==table['get'] and update['function']==table['replace'] and len(ua)==3 and ua[1]==ga[1]:
                            target={'Match':dict(scrutinee=call(table['get'],[ua[0],ga[1]]),branches=branches)}
                            return t,target,law,[ua[0],ga[1],ua[2]]
            if isinstance(t,dict):
                for key in sorted(t):
                    r=find(t[key])
                    if r:return r
            if isinstance(t,list):
                for x in t:
                    r=find(x)
                    if r:return r
            return None
        def replace(t,target,value):
            if t==target:return copy.deepcopy(value)
            if isinstance(t,dict):return {k:replace(v,target,value) for k,v in t.items()}
            if isinstance(t,list):return [replace(v,target,value) for v in t]
            return t
        for _ in range(64):
            found=find(current)
            if not found:break
            original,replacement,law,args=found
            context=replace(current,original,var('replacement_rows'))
            steps.append({'Substitute':dict(variable='replacement_rows',context=context,equality={'Instance':dict(**law,arguments=args,premises=[])})})
            current=replace(current,original,replacement)
        # Convert rechecks the final complete observation, including hygienic
        # binder changes caused by removing a statement. Syntactic identity is
        # unnecessarily strict here; this proposal gains no authority from it.
        current,left_steps=canonical(current)
        end_canonical,right_steps=canonical(end)
        if right_steps:
            tail=trans(guarded_equality(current,end_canonical,objects),{'Sym':trans(*right_steps)},convert(end,new))
        else:
            tail=guarded_equality(current,new,objects)
        case=trans(convert(old,start),*steps,*left_steps,tail)
        args=[var(n) for n,_ in a['params']]
        proofs[name]={'Induction':dict(variable='initial',**{'from':call(a['function'],args),'to':call(z['function'],args)},cases=[dict(bindings=a['case']['bindings'],proof=case)])}
    roots=sorted({a['function'] for a in before['actions'].values()}|{a['function'] for a in after['actions'].values()}|{law['theorem'] for law in laws.values()}|{law['theorem'] for _,_,law in coalescing}|used_commuting)
    store=Store.publish(directory,list(objects.values()))
    return dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=before['source'],knowledge=store.bundle(roots),applications=[],action_replacement=dict(selected=selected,proofs=proofs))

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('before');p.add_argument('after');p.add_argument('selected');p.add_argument('-o','--output',required=True);p.add_argument('--knowledge',type=Path);p.add_argument('--snapshot',type=Path)
    a=p.parse_args();out=Path(a.output);out.parent.mkdir(parents=True,exist_ok=True)
    result=produce(read(Path(a.before)),read(Path(a.after)),read(Path(a.selected)),out.parent/'database',a.knowledge,a.snapshot)
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='proposed',authority='requires compiler checking')))
if __name__=='__main__':main()
