"""Database-owned, universally checked equality-guarded word replacement.

This recipe only proposes implementations. The normal maintained-fold admission
replays both the previous update equation and the complete 64-bit RUP proof.
No source names, profiles, bounded samples or trusted arithmetic matcher grant
permission to skip work.
"""
import copy, gzip, json
from pathlib import Path
from ink_knowledge import Store, identity
from ink_knowledge.store import entry
from producers.action_replacement import var, call, convert, trans
from producers.point_delta import binary, normal
from producers.representations import refs


def guarded_word_update(package, directory, zero=False):
    package=copy.deepcopy(package)
    objects=package['knowledge']['objects']
    proof_name='word-update-guarded-zero.json.gz' if zero else 'word-update-equal.json.gz'
    proof=json.loads(gzip.decompress((Path(__file__).parent/'data'/proof_name).read_bytes()))
    original=proof['BitVector']['from'];guarded=proof['BitVector']['to']
    params=[['total','U64'],['old','U64'],['new','U64']]
    def add(kind,declaration):
        payload=dict(declaration=declaration);body=next(iter(declaration.values()))
        obj=entry(kind,'first-order-inductive-equality-v1',payload,refs(payload),parameters=dict(body['params']),result=body.get('result'),conditions=body.get('conditions',[]))
        key=identity(obj);objects[key]=obj;return key
    theorem=None;function=None;changed=0
    for view in package['views']:
        previous=view.get('update')
        if not previous:continue
        old=call(previous['function'],[var(n) for n,_ in params])
        # This is an untrusted applicability hint, followed by Convert admission.
        if normal(old,objects)!=original:continue
        if theorem is None:
            theorem=add('theorem',{'Theorem':dict(params=params,conditions=[],**{'from':original,'to':guarded},proof=proof)})
            function=add('definition',{'Function':dict(params=params,result='U64',body=guarded,recursive=None)})
        new=call(function,[var(n) for n,_ in params])
        view['update']=dict(function=function,proof=trans(previous['proof'],convert(old,original),{'Use':dict(theorem=theorem,arguments=[var(n) for n,_ in params],premises=[])},convert(guarded,new)))
        changed+=1
    if not changed:raise ValueError('no checked word replacement proposal applies')
    store=Store.publish(Path(directory),list(objects.values()))
    package['knowledge']=store.bundle(sorted(objects))
    return package
