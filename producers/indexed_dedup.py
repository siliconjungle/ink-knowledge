"""Compose external proof libraries for an exact ordered word-set alternative.

Authoring is ordinary emit-laws. This module does not select an implementation,
install a compiler rewrite, or assert that an index is profitable for small lists.
Automatic source-extension proposal integration is separate.
"""
import json
from pathlib import Path
from producers.map_algebra import documents as map_documents

def documents(word_type='U32'):
    if word_type not in ['U32','U64','I32']:raise ValueError('unsupported indexed word type')
    libraries=Path(__file__).resolve().parents[1]/'libraries'
    source,proofs=map_documents()
    for name in ['fold-representations.ink','boolean-folds.ink','indexed-dedup-u32.ink']:
        part=(libraries/name).read_text().split('\n',1)[1]
        if name=='indexed-dedup-u32.ink':part=part.replace('u32',word_type.lower())
        source+='\n'+part
    return source,proofs

def write(directory):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    source,proofs=documents();(directory/'source.ink').write_text(source)
    (directory/'proofs.json').write_text(json.dumps(proofs,indent=2)+'\n')
    return directory/'source.ink',directory/'proofs.json'

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('output');args=parser.parse_args();write(args.output)
