"""Publish independently replayable capability dependencies and codec proofs.

Source capabilities require check-physical-plan with their source and layouts.
The generic knowledge verifier deliberately does not treat them as rewrites.
"""
import argparse,json
from pathlib import Path
from ink_knowledge import Store,identity,canonical
from ink_knowledge.store import entry,read
from producers.physical_capabilities import MATH,var

def publish(root,plans,selection=None):
 st=Store(root);objects={};names=st.names;codec_roots=set();cap_roots=set();fusion_roots=set()
 for path in plans:
  package=read(path)
  for step in package['steps']:
   if step['kind']!='physical':continue
   p=step['package']
   for l in p['columns']:
    objects.update(l['knowledge']['objects']);codec_roots.add(l['roundtrip']);names['columns/roundtrip/'+l['record']]=l['roundtrip']
    for field,packing in l['packing'].items():
     bits=packing['bits'];mask=(1<<bits)-1;v=var('value');binary=lambda op:{'Binary':dict(op=op,left=v,right={'U64':mask})};conditions=[dict(**{'from':binary('<='),'to':{'Bool':True}})];a,z=binary('&'),v
     theorem=dict(params=[['value','U64']],conditions=conditions,**{'from':a,'to':z},proof={'BitVector':dict(**{'from':a,'to':z},hypotheses=[0],certificate=packing['proof'])})
     obj=entry('theorem',MATH,dict(declaration={'Theorem':theorem}),parameters={'value':'U64'},conditions=conditions);ident=identity(obj);objects[ident]=obj;codec_roots.add(ident);names[f'columns/packing/{bits}']=ident
   for key in ['bounds','column_maps']:
    if key in p:
     objects.update(p[key]['knowledge']['objects']);cap_roots.update(p[key]['knowledge']['roots'])
 if selection:
  p=read(selection);objects.update(p['knowledge']['objects']);fusion_roots.update(p['knowledge']['roots'])
  for app in p['applications']:names['fusion/carrier/'+app['function']]=app['law']
 st=st.extend(list(objects.values()),names)
 # Existing views remain pinned to their immutable snapshots. Only these new
 # transport views use the new publication; no old proof bytes are rewritten.
 for name,roots in [('column-codec',codec_roots),('source-capabilities',cap_roots),('carrier-fusion',fusion_roots)]:
  (st.data/(name+'-view.json')).write_bytes(canonical(st.bundle(sorted(roots)))+b'\n')
 return st

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--knowledge-root',type=Path,required=True);p.add_argument('--plan',type=Path,action='append',required=True);p.add_argument('--selection',type=Path);a=p.parse_args();st=publish(a.knowledge_root,a.plan,a.selection);print(st.snapshot_id)
if __name__=='__main__':main()
