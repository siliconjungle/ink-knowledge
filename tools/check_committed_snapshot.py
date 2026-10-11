"""Check that a clean checkout contains the active authenticated catalogue."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from ink_knowledge import Store


def check(root):
    tracked = set(subprocess.check_output(
        ['git', '-C', str(root), 'ls-tree', '-r', '--name-only', 'HEAD', 'store'],
        text=True).splitlines())
    store = Store(root)
    members = store.members()  # Authenticate the tree before examining its paths.
    pending = [store.snapshot['root']]
    seen = set()
    while pending:
        key = pending.pop()
        if key in seen:
            continue
        seen.add(key)
        path = 'store/trees/' + key + '.json'
        if path not in tracked:
            raise ValueError('active tree missing from committed checkout: ' + path)
        node = json.loads((root / path).read_bytes())
        if 'entries' not in node:
            pending.extend([node['left'], node['right']])
    for key in members:
        path = 'store/objects/' + key + '.json'
        if path not in tracked:
            raise ValueError('active member missing from committed checkout: ' + path)
    print(json.dumps(dict(status='complete', snapshot=store.snapshot_id,
                          members=len(members), trees=len(seen))))


if __name__ == '__main__':
    check(ROOT)
