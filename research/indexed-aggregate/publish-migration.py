"""Admit and publish the fixture's direct-to-indexed migration and compact pin."""
import argparse, hashlib, json, sys, subprocess
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from ink_knowledge import Store, canonical
from ink_knowledge.store import read, immutable

p = argparse.ArgumentParser(description=__doc__)
for field in ('compiler', 'source', 'before', 'after', 'bridge', 'database', 'root', 'report'):
    p.add_argument('--' + field, type=Path, required=True)
a = p.parse_args()
receipt = json.loads(subprocess.run([
    str(a.compiler.resolve()), 'check-migration', str(a.source.resolve()),
    str(a.before.resolve()), str(a.after.resolve()), str(a.bridge.resolve())
], check=True, capture_output=True, text=True).stdout)
before, after, bridge = [read(path) for path in (a.before, a.after, a.bridge)]
if (receipt.get('status'), receipt.get('from'), receipt.get('to'), receipt.get('migration')) != (
        'checked', before['representation'], after['representation'], bridge['root']):
    raise ValueError('migration admission receipt mismatch')
old, staged = Store(a.root), Store(a.database)
objects = {i: old.object(i) for i in old.members()}
objects.update({i: staged.object(i) for i in staged.members()})
names = read(a.root / 'store/names.json')
names.update({'indexed-aggregate/direct': before['representation'],
              'indexed-aggregate/migration': bridge['root']})
published = Store.publish(a.root, objects.values(), names, leaf_size=2)
for directory in ('trees', 'snapshots'):
    for path in (a.database / 'store' / directory).glob('*.json'):
        immutable(a.root / 'store' / directory / path.name, read(path))
pin = a.root / 'store/snapshots' / (staged.snapshot_id + '.json')
if canonical(Store(a.root, snapshot=pin).bundle([bridge['root']])) != canonical(bridge['knowledge']):
    raise ValueError('published migration pin differs from admitted packet')
published.rebuild()
result = dict(status='checked', source=before['input_core_sha256'],
              previous_snapshot=old.snapshot_id, snapshot=published.snapshot_id,
              view_snapshot=staged.snapshot_id, migration=bridge['root'],
              before=before['representation'], after=after['representation'],
              obligations=len(receipt['obligations']),
              request_sha256=hashlib.sha256(a.bridge.read_bytes()).hexdigest())
a.report.write_bytes(canonical(result) + b'\n')
print(json.dumps(result))
