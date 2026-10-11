"""Untrusted total upsert and ordered batch aggregate laws.

Recognising a source helper only proposes a theorem. General equality and
induction checking authorise every equation, including duplicate/unordered rows.
"""
from action_replacement import var, call, convert, trans
from point_delta import binary, choice, match, sub, normal, replace, lift


def extend(model, table, q, contribution, delta_functions, updates, add, objects, arithmetic):
    functions={n:table[n] for n in updates}
    row_argument={n:0 for n in updates}
    d=table['datatype'];rows=var('bulk_rows');key=var('bulk_key');value=var('bulk_value')
    row_sort=objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    key_sort=objects[table['get']]['payload']['declaration']['Function']['params'][1][1]
    definitions=[(i,o['payload']['declaration']['Function']) for i,o in list(objects.items()) if 'Function' in o['payload'].get('declaration',{})]
    def theorem(params,a,z,p):return add({'Theorem':dict(params=params,conditions=[],**{'from':a,'to':z},proof=p)})
    def function(params,body):return add({'Function':dict(params=params,result='U64',body=body,recursive=None)})
    def reduced(term,guard,flag):
        before=normal(term,objects);after=replace(before,normal(guard,objects),{'Bool':flag})
        return trans(convert(term,before),lift({'Hypothesis':0},replace(before,normal(guard,objects),var('delta_hole'))),convert(after,normal(after,objects)))
    puts={}
    for i,f in definitions:
        ps=f['params']
        if len(ps)!=3 or [t for _,t in ps]!=[{'Data':d},key_sort,row_sort]:continue
        r,k,v=map(var,[n for n,_ in ps]);guard=call(table['contains'],[r,k])
        expected=choice(guard,call(table['replace'],[r,k,v]),call(table['insert'],[r,k,v]))
        if f['body']!=expected:continue
        name='put:'+i
        params=[['bulk_rows',{'Data':d}],['bulk_key',key_sort],['bulk_value',row_sort]]
        guard=call(table['contains'],[rows,key]);diff=choice(guard,call(delta_functions['replace'],[rows,key,value]),call(contribution,[value]))
        delta_functions[name]=function(params,diff)
        a=q(call(i,[rows,key,value]));z=binary('+',q(rows),call(delta_functions[name],[rows,key,value]));branches={}
        for label,flag,operation in [('on_false',False,'insert'),('on_true',True,'replace')]:
            target=q(call(table[operation],[rows,key,value]))
            tail=binary('+',q(rows),call(contribution,[value]) if operation=='insert' else call(delta_functions['replace'],[rows,key,value]))
            branches[label]=trans(reduced(a,guard,flag),convert(normal(replace(normal(a,objects),normal(guard,objects),{'Bool':flag}),objects),target),
                {'Use':dict(theorem=updates[operation],arguments=[rows,key,value],premises=[])},
                convert(tail,normal(replace(normal(z,objects),normal(guard,objects),{'Bool':flag}),objects)),{'Sym':reduced(z,guard,flag)})
        updates[name]=theorem(params,a,z,{'BoolSplit':dict(condition=guard,**{'from':a,'to':z},**branches)})
        functions[name]=i;row_argument[name]=0;puts[i]=name
    # Batch operations recurse over keys and carry the evolving rows. The
    # generalised induction hypothesis may be instantiated at those new rows.
    for i,f in definitions:
        ps=f['params'];body=f['body'].get('Match',{})
        if len(ps) not in (2,3) or f['result']!={'Data':d} or not body:continue
        if ps[-1][1]!={'Data':d} or body['scrutinee']!=var(ps[0][0]):continue
        cs=objects.get(ps[0][1].get('Data'),{}).get('payload',{}).get('declaration',{}).get('Datatype',{}).get('constructors',[])
        if len(cs)!=2 or cs[0]['fields'] or cs[1]['fields']!=[key_sort,'SelfType']:continue
        branches=body['branches']
        if len(branches)!=2 or branches[0]['body']!=var(ps[-1][0]):continue
        ks,rs=var(ps[0][0]),var(ps[-1][0]);bn=branches[1]['bindings']
        if len(bn)!=2:continue
        hk,kt=map(var,bn)
        kind=None;put=None
        if len(ps)==2:
            if branches[1]['body']=={'SelfCall':[kt,call(table['remove'],[rs,hk])]}:kind='remove'
        else:
            vb=branches[1]['body'].get('Match',{})
            if vb.get('scrutinee')!=var(ps[1][0]) or len(vb.get('branches',[]))!=2:continue
            if vb['branches'][0]['body']!=rs or len(vb['branches'][1]['bindings'])!=2:continue
            hv,vt=map(var,vb['branches'][1]['bindings'])
            for pid,pname in puts.items():
                if vb['branches'][1]['body']=={'SelfCall':[kt,vt,call(pid,[rs,hk,hv])]}:kind='put';put=pname
        if kind is None:continue
        name='batch:'+i
        params=ps
        head=call(delta_functions['remove'],[rs,hk]) if kind=='remove' else call(delta_functions[put],[rs,hk,hv])
        new=call(table['remove'],[rs,hk]) if kind=='remove' else call(functions[put],[rs,hk,hv])
        recur={'SelfCall':[kt,*([vt] if kind=='put' else []),new]}
        step=binary('+',head,recur)
        if kind=='put':step=match(var(ps[1][0]),[([],{'U64':0}),(vb['branches'][1]['bindings'],step)])
        difference=add({'Function':dict(params=params,result='U64',body=match(ks,[([],{'U64':0}),(bn,step)]),recursive=0)})
        delta_functions[name]=difference;functions[name]=i;row_argument[name]=len(ps)-1
        args=[var(n)for n,_ in ps]
        a=q(call(i,args));z=binary('+',q(rs),call(difference,args))
        bound=lambda keylist,values=None:sub(a,{ps[0][0]:keylist,**({ps[1][0]:values}if values is not None else{})})
        right=lambda keylist,values=None:sub(z,{ps[0][0]:keylist,**({ps[1][0]:values}if values is not None else{})})
        from action_replacement import cons
        nil=cons(ps[0][1]['Data'],0,[]);conskeys=cons(ps[0][1]['Data'],1,[hk,kt])
        old= q(rs);delta=head;future=call(difference,[kt,*([vt]if kind=='put'else[]),new])
        def nonempty(left,right):
            hypothesis={'GeneralizedHypothesis':dict(index=0,arguments=[*([vt]if kind=='put'else[]),new])}
            qnew=q(new);middle=binary('+',qnew,future)
            law=updates['remove']if kind=='remove'else updates[put]
            lawargs=[rs,hk,*([hv]if kind=='put'else[])]
            changed=binary('+',binary('+',old,delta),future)
            grouped=binary('+',old,binary('+',delta,future))
            return trans(convert(left,q(call(i,[kt,*([vt]if kind=='put'else[]),new]))),hypothesis,
                lift({'Use':dict(theorem=law,arguments=lawargs,premises=[])},binary('+',var('delta_hole'),future)),arithmetic(changed,grouped),convert(grouped,right))
        left,right=bound(conskeys),right(conskeys)
        if kind=='put':
            vn=cons(ps[1][1]['Data'],0,[]);vc=cons(ps[1][1]['Data'],1,[hv,vt])
            p={'Induction':dict(variable=ps[1][0],**{'from':left,'to':right},cases=[
                dict(bindings=[],proof=arithmetic(normal(sub(left,{ps[1][0]:vn}),objects),normal(sub(right,{ps[1][0]:vn}),objects))),
                dict(bindings=vb['branches'][1]['bindings'],proof=nonempty(sub(left,{ps[1][0]:vc}),sub(right,{ps[1][0]:vc})))])}
        else:p=nonempty(left,right)
        zero_left=bound(nil);zero_right=sub(z,{ps[0][0]:nil})
        base=trans(convert(zero_left,old),arithmetic(old,binary('+',old,{'U64':0})),convert(binary('+',old,{'U64':0}),zero_right))
        proof={'GeneralizedInduction':dict(variable=ps[0][0],generalize=[n for n,_ in ps[1:]],**{'from':a,'to':z},cases=[dict(bindings=[],proof=base),dict(bindings=bn,proof=p)])}
        updates[name]=theorem(params,a,z,proof)
    return functions,row_argument
