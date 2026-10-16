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
from ink_knowledge import canonical, identity, semantic_entry

SEMANTICS = 'ink-frozen-law-index-v1'
DEPENDENCY_SEMANTICS = 'ink-frozen-law-index-v2'
MAX_PROOF_BYTES = 16_000_000


def _write(path, data):
    fd, name = tempfile.mkstemp(prefix='.frozen-laws-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(data)
        os.replace(name, path)
    finally:
        if os.path.exists(name):
            os.unlink(name)


def _packet(directory):
    directory = Path(directory)
    packet = json.loads((directory/'index.json').read_bytes())
    legacy = (set(packet) == {'schema','semantics','rows'} and
              packet['schema'] == 1 and packet['semantics'] == SEMANTICS)
    dependent = (set(packet) == {'schema','semantics','rows','objects'} and
                 packet['schema'] == 2 and packet['semantics'] == DEPENDENCY_SEMANTICS)
    if (not (legacy or dependent) or not isinstance(packet['rows'], list) or
            len(packet['rows']) > 4096):
        raise ValueError('Frozen law index schema or budget')
    def digest(s):
        return isinstance(s,str) and len(s)==64 and all(c in '0123456789abcdef' for c in s)
    if dependent and (not isinstance(packet['objects'],dict) or len(packet['objects']) > 4096 or
                      any(not digest(k) or not digest(v) for k,v in packet['objects'].items())):
        raise ValueError('Frozen dependency index schema or budget')
    names = set()
    for row in packet['rows']:
        if (set(row) != {'name','sha256','params','from'} or
                not isinstance(row['name'],str) or row['name'] in names or
                not isinstance(row['sha256'],str) or len(row['sha256']) != 64 or
                any(c not in '0123456789abcdef' for c in row['sha256'])):
            raise ValueError('Frozen law index row')
        names.add(row['name'])
    return packet


def index(directory):
    return _packet(directory)['rows']


def _load_proof(directory, digest):
    with gzip.open(Path(directory)/(digest+'.json.gz'),'rb') as source:
        raw = source.read(MAX_PROOF_BYTES + 1)
    if len(raw) > MAX_PROOF_BYTES:
        raise ValueError('Frozen proof byte limit')
    law = json.loads(raw)
    if identity(law) != digest:
        raise ValueError('Frozen law index/proof mismatch')
    return law


def load(directory, row):
    law = _load_proof(directory, row['sha256'])
    if law['params'] != row['params'] or law['from'] != row['from']:
        raise ValueError('Frozen law index/proof mismatch')
    return law


def read(directory):
    return [dict(name=row['name'],law=load(directory,row)) for row in index(directory)]


def update(directory, rows, *, dependencies=()):
    """Append checked acquisitions without erasing earlier partial batches."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    with (directory/'.authoring.lock').open('a+') as mutex:
        fcntl.flock(mutex, fcntl.LOCK_EX)
        prior = _packet(directory) if (directory/'index.json').exists() else dict(rows=[])
        merged = {row['name']:row for row in prior['rows']}
        objects = dict(prior.get('objects',{}))
        def store(law):
            digest = identity(law)
            path = directory/(digest+'.json.gz')
            data = canonical(law)
            if len(data) > MAX_PROOF_BYTES:
                raise ValueError('Frozen proof byte limit')
            if path.exists():
                with gzip.open(path,'rb') as source:
                    existing = source.read(MAX_PROOF_BYTES + 1)
                if existing != data:
                    raise ValueError('Frozen proof content mismatch')
            else:
                _write(path, gzip.compress(data,mtime=0))
            return digest
        for row in rows:
            law = row['law']; digest = store(law)
            merged[row['name']] = dict(name=row['name'],sha256=digest,params=law['params'],**{'from':law['from']})
        for law in dependencies:
            objects[identity(semantic_entry(law))] = store(law)
        packet = dict(schema=1,semantics=SEMANTICS,rows=[merged[name] for name in sorted(merged)])
        if len(packet['rows']) > 4096:
            raise ValueError('Frozen law index budget')
        if objects or prior.get('schema') == 2:
            if len(objects) > 4096:
                raise ValueError('Frozen dependency index budget')
            packet.update(schema=2,semantics=DEPENDENCY_SEMANTICS,objects=objects)
        _write(directory/'index.json',canonical(packet)+b'\n')
    return len(merged)


def matching_rows(subject, rows):
    from ink_planner.semantic_search import positions, match
    from ink_knowledge.pattern_index import TermIndex
    sites = [t for body in subject.get('functions',{}).values() for _, t in positions(body)]
    if not sites:
        return []
    terms = TermIndex(sites)
    return [row for row in rows
                if any(match(row['from'],t,row['params'],{})
                       for t in terms.candidates(row['from'], row['params']))]


def closure(directory, named_laws, *, prefix='', maximum_entries=256):
    """Load only exact supporting objects, before their consumers.

    V1 retains its existing external-store dependency behavior. V2 explicitly
    maps entry identities to frozen proof files. Neither map nor a successful
    content hash check grants mathematical authority: ordinary catalogue replay
    must still prove every object and every source application.
    """
    packet = _packet(directory)
    if packet['schema'] == 1:
        return list(named_laws)
    if type(maximum_entries) is not int or not 1 <= maximum_entries <= 1024:
        raise ValueError('Frozen dependency closure bound')
    if len(named_laws) > maximum_entries:
        raise ValueError('Frozen dependency closure budget')
    if not any(law.get('dependencies') for _,law in named_laws):
        return list(named_laws)
    supplied = {identity(semantic_entry(law)):(name,law) for name,law in named_laws}
    output, finished, visiting = [], set(), set()
    def visit(ident, depth):
        if ident in finished:
            return
        if depth > 64 or len(finished) + len(visiting) >= maximum_entries:
            raise ValueError('Frozen dependency closure budget')
        if ident in visiting:
            raise ValueError('Frozen dependency cycle')
        visiting.add(ident)
        if ident in supplied:
            name,law = supplied[ident]
        else:
            digest = packet['objects'].get(ident)
            if digest is None:
                raise ValueError('Frozen dependency missing from index')
            law = _load_proof(directory,digest)
            if identity(semantic_entry(law)) != ident:
                raise ValueError('Frozen dependency entry/proof mismatch')
            name = prefix+'dependency/'+ident
        for child in law.get('dependencies',[]):
            visit(child,depth+1)
        visiting.remove(ident)
        finished.add(ident)
        output.append((name,law))
    for ident in supplied:
        visit(ident,0)
    return output


def specialize(subject, directory, prefix):
    # Preserve the no-input/no-decompression fast path.
    if not subject.get('functions'):
        return []
    rows = matching_rows(subject,index(directory))
    selected = [(prefix+row['name'],load(directory,row)) for row in rows]
    return closure(directory,selected,prefix=prefix) if selected else []
