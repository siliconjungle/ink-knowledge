"""Exact two-bucket point index over ordinary columns, with universal proofs.

The base columns retain exact logical order for snapshots. Buckets retain order
and duplicate keys. Rebuilding buckets after a physical mutation is deliberate:
there is no sorted/unique-row premise or trusted index invariant.
"""
import json, os, subprocess, tempfile
from pathlib import Path
from action_replacement import var,call,cons,convert,trans
from point_delta import binary,choice,match,sub,normal,equality,lift,replace
from cache_maintenance import variables


def prepare(table, root_sort, cid, columns, selectors, encode, decode, roundtrip,
            point, point_law, operations, operation_laws, function, theorem, datatype, objects):
    if objects[table['get']]['payload']['declaration']['Function']['params'][1][1]!='U64':
        raise ValueError('bucket index currently supports u64 keys')
    csort={'Data':cid};d=table['datatype'];nil=cons(d,0,[])
    rows,head,row,tail,key=map(var,['index_rows','index_head','index_row','index_tail','index_key'])
    bound=cons(d,1,[head,row,tail])
    odd=lambda x:binary('!=',binary('&',x,{'U64':1}),{'U64':0})
    compiler=Path(os.environ.get('INK_COMPILER','target/debug/ink')).resolve()
    def scalar(a,z,facts):
        from bitvector_proofs import certificate
        names=sorted(variables([a,z,[list(f[:2])for f in facts]]))
        goal=dict(params=[[n,'U64']for n in names],conditions=[{'from':a,'to':z}for a,z,_ in facts],**{'from':a,'to':z})
        with tempfile.TemporaryDirectory(prefix='ink-index-law-')as temporary:
            p=Path(temporary);(p/'goal.json').write_text(json.dumps(goal))
            result=subprocess.run([str(compiler),'bitvector-obligation',str(p/'goal.json'),'-o',str(p/'cnf.json')],capture_output=True,text=True)
            if result.returncode:raise ValueError(result.stderr)
            return {'BitVector':dict(**{'from':a,'to':z},hypotheses=[f[2]for f in facts],certificate=certificate(json.loads((p/'cnf.json').read_text())))}
    use=lambda law,args,premises=[]:{'Use':dict(theorem=law,arguments=args,premises=premises)}
    bucket_functions=[];bucket_laws=[]
    for flag in [False,True]:
        keep=lambda k:odd(k) if flag else binary('==',binary('&',k,{'U64':1}),{'U64':0})
        filter_rows=function([['index_rows',root_sort]],root_sort,match(rows,[([],nil),(['index_head','index_row','index_tail'],choice(keep(head),cons(d,1,[head,row,{'SelfCall':[tail]}]),{'SelfCall':[tail]}))]),recursive=0)
        filtered=lambda r:call(filter_rows,[r])
        col_functions=[];col_laws=[]
        for i,column in enumerate(columns):
            params=[['index_keys',columns[0]],*([]if i==0 else[['index_cells',column]])]
            recur={'SelfCall':[var('index_keys_tail'),*([]if i==0 else[var('index_cells_tail')])]}
            body=choice(keep(var('index_column_key')),cons(column['Data'],1,[var('index_column_key')if i==0 else var('index_cell'),recur]),recur)
            if i:body=match(var('index_cells'),[([],cons(column['Data'],0,[])),(['index_cell','index_cells_tail'],body)])
            body=match(var('index_keys'),[([],cons(column['Data'],0,[])),(['index_column_key','index_keys_tail'],body)])
            f=function(params,column,body,recursive=0);col_functions.append(f)
            direct=lambda r:call(f,[call(selectors[0],[r]),*([]if i==0 else[call(selectors[i],[r])])])
            source=lambda r:call(selectors[i],[filtered(r)])
            a,z=direct(bound),source(bound);guard=keep(head)
            step={'BoolSplit':dict(condition=guard,**{'from':a,'to':z},**{
                name:equality(a,z,objects,(direct(tail),source(tail),0),[(guard,{'Bool':v},1)])for name,v in [('on_false',False),('on_true',True)]})}
            left,right=direct(rows),source(rows)
            col_laws.append(theorem([['index_rows',root_sort]],left,right,{'Induction':dict(variable='index_rows',**{'from':left,'to':right},cases=[dict(bindings=[],proof=convert(direct(nil),source(nil))),dict(bindings=['index_head','index_row','index_tail'],proof=step)])}))
        ns=['index_column_'+str(i)for i in range(len(columns))]
        bucket=function([['index_base',csort]],csort,match(var('index_base'),[(ns,cons(cid,0,[call(f,[var(ns[0]),*([]if i==0 else[var(ns[i])])])for i,f in enumerate(col_functions)]))]))
        left=call(bucket,[call(encode,[rows])]);right=call(encode,[filtered(rows)])
        bucket_law=theorem([['index_rows',root_sort]],left,right,trans(convert(left,cons(cid,0,[call(f,[call(selectors[0],[rows]),*([]if i==0 else[call(selectors[i],[rows])])])for i,f in enumerate(col_functions)])),{'Construct':dict(datatype=cid,constructor=0,arguments=[use(law,[rows])for law in col_laws])},convert(cons(cid,0,[call(s,[filtered(rows)])for s in selectors]),right)))
        # Under a matching query bucket, filtering preserves first-match lookup
        # for every row sequence, including unordered rows and duplicate keys.
        q=lambda r:call(table['get'],[r,key]);lhs=lambda r:q(filtered(r));rhs=q
        query_guard=odd(key);condition={'from':query_guard,'to':{'Bool':flag}}
        equal=binary('==',key,head);keep_guard=keep(head)
        a,z=lhs(bound),rhs(bound)
        def branch(equal_flag):
            facts=[(query_guard,{'Bool':flag},0),(equal,{'Bool':equal_flag},2)]
            if equal_flag:
                facts.append((keep_guard,{'Bool':True},scalar(keep_guard,{'Bool':True},facts)))
                return equality(a,z,objects,(lhs(tail),rhs(tail),1),facts)
            return {'BoolSplit':dict(condition=keep_guard,**{'from':a,'to':z},**{
                name:equality(a,z,objects,(lhs(tail),rhs(tail),1),[*facts,(keep_guard,{'Bool':v},3)])for name,v in [('on_false',False),('on_true',True)]})}
        proof={'Induction':dict(variable='index_rows',**{'from':lhs(rows),'to':rhs(rows)},cases=[dict(bindings=[],proof=convert(lhs(nil),rhs(nil))),dict(bindings=['index_head','index_row','index_tail'],proof={'BoolSplit':dict(condition=equal,**{'from':a,'to':z},on_false=branch(False),on_true=branch(True))})])}
        carriers=[i for i,o in objects.items()if 'Datatype'in o['payload'].get('declaration',{})]
        # The supplied theorem helper has empty conditions; define this ordinary
        # conditional lemma through its underlying authoring callback instead.
        get_law=theorem([['index_rows',root_sort],['index_key','U64']],lhs(rows),rhs(rows),proof,conditions=[condition])
        bucket_functions.append(bucket);bucket_laws.append((bucket_law,get_law,filter_rows))
    indexed_id=datatype([dict(name='IndexedColumns',fields=[csort,csort,csort])])
    indexed={'Data':indexed_id}
    wrap=function([['index_base',csort]],indexed,cons(indexed_id,0,[var('index_base'),*[call(f,[var('index_base')])for f in bucket_functions]]))
    encoded=function([['index_rows',root_sort]],indexed,call(wrap,[call(encode,[rows])]))
    decoded=function([['indexed',indexed]],root_sort,match(var('indexed'),[(['index_base','index_even','index_odd'],call(decode,[var('index_base')]))]))
    new_roundtrip=theorem([['index_rows',root_sort]],call(decoded,[call(encoded,[rows])]),rows,trans(convert(call(decoded,[call(encoded,[rows])]),call(decode,[call(encode,[rows])])),use(roundtrip,[rows])))
    new_operations={};new_laws={}
    for name,operation in operations.items():
        original=objects[operation]['payload']['declaration']['Function'];rest=original['params'][1:];args=[var(n)for n,_ in rest]
        f=function([['indexed',indexed],*rest],indexed,match(var('indexed'),[(['index_base','index_even','index_odd'],call(wrap,[call(operation,[var('index_base'),*args])]))]))
        changed=call(table[name],[rows,*args]);left=call(f,[call(encoded,[rows]),*args]);right=call(encoded,[changed])
        law=use(operation_laws[name],[rows,*args])
        proof=trans(convert(left,call(wrap,[call(operation,[call(encode,[rows]),*args])])),lift(law,call(wrap,[var('delta_hole')])),convert(call(wrap,[call(encode,[changed])]),right))
        new_operations[name]=f;new_laws[name]=theorem([['index_rows',root_sort],*rest],left,right,proof)
    get_result=objects[table['get']]['payload']['declaration']['Function']['result']
    point_body=match(var('indexed'),[(['index_base','index_even','index_odd'],choice(odd(key),call(point,[var('index_odd'),key]),call(point,[var('index_even'),key])))])
    indexed_point=function([['indexed',indexed],['index_key','U64']],get_result,point_body)
    left=call(indexed_point,[call(encoded,[rows]),key]);right=call(table['get'],[rows,key]);branches={}
    for label,flag in [('on_false',False),('on_true',True)]:
        law,lookup_law,filter_rows=bucket_laws[int(flag)];bucket=bucket_functions[int(flag)];filtered=call(filter_rows,[rows])
        selected=call(point,[call(bucket,[call(encode,[rows])]),key])
        reduced=normal(left,objects)
        start=trans(convert(left,reduced),lift({'Hypothesis':0},replace(reduced,odd(key),var('delta_hole'))),convert(replace(reduced,odd(key),{'Bool':flag}),selected))
        branches[label]=trans(start,lift(use(law,[rows]),call(point,[var('delta_hole'),key])),use(point_law,[filtered,key]),use(lookup_law,[rows,key],[{'Hypothesis':0}]))
    indexed_point_law=theorem([['index_rows',root_sort],['index_key','U64']],left,right,{'BoolSplit':dict(condition=odd(key),**{'from':left,'to':right},**branches)})
    return dict(sort=indexed,encode=encoded,decode=decoded,roundtrip=new_roundtrip,point=indexed_point,point_law=indexed_point_law,operations=new_operations,operation_laws=new_laws,wrap=wrap)
