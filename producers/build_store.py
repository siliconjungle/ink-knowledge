#!/usr/bin/env python3
"""Reproduce the initial canonical snapshot from explicitly quarantined research fixtures.
This is an authoring/import tool, never a production discovery path.
"""
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from ink_knowledge import Store,entry,identity,semantic_entry,canonical
from semantic_laws import examples

def build(output):
    source={};names={};objects={};translated={};active=set()
    for p in sorted((ROOT/'research').glob('**/objects/*.json')):
        v=json.loads(p.read_text());source[p.stem]=v
        names[str(p.parent.parent.relative_to(ROOT/'research'))+'/'+v.get('name',p.stem)]=p.stem
    def remap(v):
        if isinstance(v,str) and v in source:return convert(v)
        if isinstance(v,list):return [remap(x) for x in v]
        if isinstance(v,dict):return {k:remap(x) for k,x in v.items()}
        return v
    def convert(old):
        if old in translated:return translated[old]
        if old in active:raise ValueError('cyclic research input')
        active.add(old);v=remap({k:x for k,x in source[old].items() if k not in ('schema','semantics','dependencies','name','kind')})
        deps=[convert(x) for x in source[old].get('dependencies',[])];sem=source[old]['semantics']
        if 'declaration' in v:
            tag,d=next(iter(v['declaration'].items()));kind='theorem' if tag=='Theorem' else 'definition'
            params=dict(d.get('params',[]));result=d.get('result');conditions=d.get('conditions',[])
        else:
            kind='definition' if source[old].get('kind')=='definition' else 'theorem'
            params=dict(v.get('params',[]));result=v.get('result');conditions=v.get('conditions',[])
            if kind=='theorem':v.setdefault('conditions',[])
        obj=entry(kind,sem,v,deps,parameters=params,result=result,conditions=conditions)
        i=identity(obj);objects[i]=obj;translated[old]=i;active.remove(old);return i
    for i in source:convert(i)
    names={n:translated[i] for n,i in names.items()};rewrites=[]
    for n,law in enumerate(examples()):
        obj=semantic_entry(law);i=identity(obj);objects[i]=obj;rewrites.append(i);names[f'rewrite/example-{n:02}']=i
    store=Store.publish(output,objects.values(),names)
    store.rebuild()
    (Path(output)/'store/rewrite-view.json').write_bytes(canonical(store.bundle(rewrites))+b'\n')
    return store
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    s=build(a.output);print(json.dumps(dict(snapshot=s.snapshot_id,entries=len(s.members()))))
