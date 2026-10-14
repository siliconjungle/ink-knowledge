"""Indexed immutable proof libraries for untrusted database discovery.

Pattern metadata permits rejection before proof decompression. It grants no
admission: every returned law still goes through the ordinary Ink checker.
Indexes are atomically replaced; content-addressed proof files are never edited.
"""
import fcntl
import gzip
import json
import os
from pathlib import Path
import tempfile
from ink_knowledge import canonical, identity

SEMANTICS = 'ink-frozen-law-index-v1'


def _write(path, data):
    fd, name = tempfile.mkstemp(prefix='.frozen-laws-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(data)
        os.replace(name, path)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def index(directory):
    directory = Path(directory)
    packet = json.loads((directory/'index.json').read_bytes())
    if (set(packet) != {'schema','semantics','rows'} or packet['schema'] != 1 or
            packet['semantics'] != SEMANTICS or not isinstance(packet['rows'], list) or
            len(packet['rows']) > 4096):
        raise ValueError('Frozen law index schema or budget')
    names = set()
    for row in packet['rows']:
        if (set(row) != {'name','sha256','params','from'} or
                not isinstance(row['name'],str) or row['name'] in names or
                not isinstance(row['sha256'],str) or len(row['sha256']) != 64 or
                any(c not in '0123456789abcdef' for c in row['sha256'])):
            raise ValueError('Frozen law index row')
        names.add(row['name'])
    return packet['rows']


def load(directory, row):
    raw = gzip.decompress((Path(directory)/(row['sha256']+'.json.gz')).read_bytes())
    law = json.loads(raw)
    if identity(law) != row['sha256'] or law['params'] != row['params'] or law['from'] != row['from']:
        raise ValueError('Frozen law index/proof mismatch')
    return law


def read(directory):
    return [dict(name=row['name'],law=load(directory,row)) for row in index(directory)]


def update(directory, rows):
    """Append checked acquisitions without erasing earlier partial batches."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    with (directory/'.authoring.lock').open('a+') as mutex:
        fcntl.flock(mutex, fcntl.LOCK_EX)
        merged = {row['name']:row for row in index(directory)} if (directory/'index.json').exists() else {}
        for row in rows:
            law = row['law']; digest = identity(law)
            path = directory/(digest+'.json.gz')
            data = canonical(law)
            if path.exists():
                if gzip.decompress(path.read_bytes()) != data:
                    raise ValueError('Frozen proof content mismatch')
            else:
                _write(path, gzip.compress(data,mtime=0))
            merged[row['name']] = dict(name=row['name'],sha256=digest,params=law['params'],**{'from':law['from']})
        packet = dict(schema=1,semantics=SEMANTICS,rows=[merged[name] for name in sorted(merged)])
        if len(packet['rows']) > 4096:
            raise ValueError('Frozen law index budget')
        _write(directory/'index.json',canonical(packet)+b'\n')
    return len(merged)


def specialize(subject, directory, prefix):
    from ink_planner.semantic_search import positions, match
    sites = [t for body in subject.get('functions',{}).values() for _, t in positions(body)]
    if not sites:
        return []
    selected = [row for row in index(directory)
                if any(match(row['from'],t,row['params'],{}) for t in sites)]
    return [(prefix+row['name'],load(directory,row)) for row in selected]
