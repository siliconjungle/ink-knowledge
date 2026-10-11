"""Prepared dense point slots with exact fallback for every other key.

A bounded prefix is an authoring choice, not a claimed source range. The base
columns retain all rows, ordering and duplicates. Universal point and mutation
proofs preserve the complete unchanged source and arbitrary future updates.
"""
import json,os,subprocess,tempfile
from pathlib import Path
from action_replacement import var,call,cons,convert,trans
from point_delta import binary,choice,match,normal,replace,lift


def prepare(table,root_sort,csort,encode,decode,roundtrip,point,point_law,
            operations,operation_laws,function,theorem,datatype,objects,size):
    if not 1<=size<=16:raise ValueError('dense slot authoring budget is 1..16')
    get=objects[table['get']]['payload']['declaration']['Function']
    if get['params'][1][1]!='U64':raise ValueError('dense prefix currently supports u64 keys')
    result=get['result'];keys=[{'U64':i}for i in range(size)]
    did=datatype([dict(name='DensePointColumns',fields=[csort,*[result for _ in keys]])]);dense={'Data':did}
    rows,key=var('dense_rows'),var('dense_key')
    wrap=function([['dense_base',csort]],dense,cons(did,0,[var('dense_base'),*[call(point,[var('dense_base'),k])for k in keys]]))
    encoded=function([['dense_rows',root_sort]],dense,call(wrap,[call(encode,[rows])]))
    names=['dense_base',*['dense_slot_'+str(i)for i in range(size)]]
    decoded=function([['dense',dense]],root_sort,match(var('dense'),[(names,call(decode,[var('dense_base')]))]))
    use=lambda law,args,premises=():{'Use':dict(theorem=law,arguments=args,premises=list(premises))}
    left=call(decoded,[call(encoded,[rows])])
    rt=theorem([['dense_rows',root_sort]],left,rows,trans(convert(left,call(decode,[call(encode,[rows])])),use(roundtrip,[rows])))
    ops,laws={},{}
    for name,operation in operations.items():
        rest=objects[operation]['payload']['declaration']['Function']['params'][1:];args=[var(n)for n,_ in rest]
        f=function([['dense',dense],*rest],dense,match(var('dense'),[(names,call(wrap,[call(operation,[var('dense_base'),*args])]))]))
        left=call(f,[call(encoded,[rows]),*args]);right=call(encoded,[call(table[name],[rows,*args])])
        proof=trans(convert(left,call(wrap,[call(operation,[call(encode,[rows]),*args])])),lift(use(operation_laws[name],[rows,*args]),call(wrap,[var('delta_hole')])),convert(call(wrap,[call(encode,[call(table[name],[rows,*args])])]),right))
        ops[name]=f;laws[name]=theorem([['dense_rows',root_sort],*rest],left,right,proof)
    body=call(point,[var('dense_base'),key])
    for i,k in reversed(list(enumerate(keys))):body=choice(binary('==',key,k),var(names[i+1]),body)
    read=function([['dense',dense],['dense_key','U64']],result,match(var('dense'),[(names,body)]))
    left=call(read,[call(encoded,[rows]),key]);right=call(table['get'],[rows,key])
    compiler=Path(os.environ.get('INK_COMPILER','target/debug/ink')).resolve()
    def scalar(target,index):
        from bitvector_proofs import certificate
        guard=binary('==',key,target);goal=dict(params=[['dense_key','U64']],conditions=[{'from':guard,'to':{'Bool':True}}],**{'from':key,'to':target})
        with tempfile.TemporaryDirectory(prefix='ink-dense-law-')as tmp:
            p=Path(tmp);(p/'goal.json').write_text(json.dumps(goal));r=subprocess.run([str(compiler),'bitvector-obligation',p/'goal.json','-o',p/'cnf.json'],capture_output=True,text=True)
            if r.returncode:raise ValueError(r.stderr)
            return {'BitVector':dict(**{'from':key,'to':target},hypotheses=[index],certificate=certificate(json.loads((p/'cnf.json').read_text())))}
    def reduced(t,facts):
        current=normal(t,objects);proof=convert(t,current)
        for guard,flag,index in facts:
            changed=replace(current,guard,{'Bool':flag})
            if changed!=current:
                proof=trans(proof,lift({'Hypothesis':index},replace(current,guard,var('delta_hole'))),convert(changed,normal(changed,objects)));current=normal(changed,objects)
        return current,proof
    def prove(index=0,facts=()):
        if index==len(keys):
            current,proof=reduced(left,facts);baseline=call(point,[call(encode,[rows]),key])
            return trans(proof,convert(current,baseline),use(point_law,[rows,key]))
        target=keys[index];guard=binary('==',key,target)
        yes_facts=(*facts,(guard,True,index));current,start=reduced(left,yes_facts)
        selected=call(point,[call(encode,[rows]),target]);source_target=call(table['get'],[rows,target])
        yes=trans(start,convert(current,selected),use(point_law,[rows,target]),{'Sym':lift(scalar(target,index),call(table['get'],[rows,var('delta_hole')]))})
        return {'BoolSplit':dict(condition=guard,**{'from':left,'to':right},on_true=yes,on_false=prove(index+1,(*facts,(guard,False,index))))}
    law=theorem([['dense_rows',root_sort],['dense_key','U64']],left,right,prove())
    return dict(sort=dense,encode=encoded,decode=decoded,roundtrip=rt,point=read,point_law=law,operations=ops,operation_laws=laws,wrap=wrap)
