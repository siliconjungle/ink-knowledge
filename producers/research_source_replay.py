#!/usr/bin/env python3
"""Replay current research packages through exact action projection and kernel checks.

Stage every proposed source binding before publication. Historical observations,
receipts and immutable proof objects retain their original compiler/source pins.
"""
import argparse, json, shutil, sys, tempfile
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store, canonical
from ink_knowledge.store import read
from ink_knowledge.implementation_candidates import identity_selection, publish_candidates
from producers.rebind_representations import replay

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--compiler', type=Path, required=True)
p.add_argument('--distribution', type=Path, required=True)
a=p.parse_args(); root=Path(__file__).resolve().parents[1]; distribution=a.distribution.resolve()
groups=[
 (distribution/'examples/point-query-delta.ink','point-delta',['direct','delta','refresh']),
 (root/'research/source-representations/app.ink','source-representations',['direct','reversed-query-cache','retained-direct','retained-query-cache']),
 (root/'research/cache-maintenance/app.ink','cache-maintenance',['direct','refresh','preserve','composed-direct','composed']),
 (root/'research/cache-maintenance/app.ink','compact-queries',['direct','cached','previous']),
 (root/'research/keep-parity/app.ink','keep-parity',['representation-0','representation-1']),
 (distribution/'examples/filtered-aggregate.ink','filtered-aggregate',['direct','refresh','sum-delta','count-delta']),
 (root/'research/storage-bulk/app.ink','storage-bulk',['direct','packed-2','packed-4','indexed-2-hot-0','indexed-4-hot-0','indexed-4-hot-1023']),
 (root/'research/storage-bulk/booleans.ink','storage-bulk',['boolean-direct','any-delta','all-delta']),
 (distribution/'examples/filtered-aggregate.ink','indexed-aggregate',['direct','request']),
]
receipts=[]; staged=[]
with tempfile.TemporaryDirectory(prefix='ink-current-source-replay-') as temporary:
 temp=Path(temporary)
 for i,(source,group,labels) in enumerate(groups):
  paths=[]
  for label in labels:
   original=root/'research'/group/(label+'.json'); proposed=temp/str(i)/(label+'.json')
   proposed.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(original,proposed)
   paths.append(proposed);staged.append((original,proposed))
  receipt=replay(a.compiler,source,paths)
  for result,label in zip(receipt['requests'],labels): result['path']=group+'/'+label+'.json'
  try: receipt['source_path']='knowledge/'+str(source.relative_to(root))
  except ValueError: receipt['source_path']=str(source.relative_to(distribution))
  receipts.append(receipt);print('checked',group,labels,flush=True)
 for original,proposed in staged: shutil.copy2(proposed,original)
 request=read(root/'research/point-delta/delta.json')
 store,ids=publish_candidates(root/'research/implementation-candidates',[identity_selection(request['input_core_sha256']),request])
 (store.root/'candidates.json').write_bytes(canonical(ids[1:])+b'\n')
 (store.root/'publication.json').write_bytes(canonical(dict(source=request['input_core_sha256'],snapshot=store.snapshot_id,baseline=ids[0],candidates=ids[1:]))+b'\n')
 direct=read(root/'research/indexed-aggregate/direct.json');indexed=read(root/'research/indexed-aggregate/request.json')
 store,ids=publish_candidates(root,[identity_selection(indexed['input_core_sha256']),direct,indexed])
 (root/'research/indexed-aggregate/implementations.json').write_bytes(canonical(dict(schema=1,source=indexed['input_core_sha256'],snapshot=store.snapshot_id,candidates=dict(zip(['source','direct','indexed'],ids))))+b'\n')
 report=dict(schema=1,status='checked',requests=sum(len(x['requests']) for x in receipts),groups=receipts,snapshot=store.snapshot_id,
  scope='Exact complete action projections and universal checking; historical measurement pins are preserved and do not transfer to these source bindings.')
 (root/'research/current-source-replay.json').write_bytes(canonical(report)+b'\n')
 print(json.dumps(dict(status='checked',requests=report['requests'],snapshot=store.snapshot_id)),flush=True)
