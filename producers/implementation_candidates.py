#!/usr/bin/env python3
"""Publish existing proof packages as implementation entries in a database."""
import argparse, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ink_knowledge.implementation_candidates import identity_selection, publish_candidates
from ink_knowledge.store import read

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--knowledge-root', type=Path, required=True)
    p.add_argument('--identity-source', action='append', default=[])
    p.add_argument('--package', type=Path, action='append', default=[])
    a = p.parse_args()
    packages = [identity_selection(i) for i in a.identity_source] + [read(f) for f in a.package]
    if not 1 <= len(packages) <= 4096:
        raise ValueError('publication requires 1..4096 candidates')
    store, candidates = publish_candidates(a.knowledge_root, packages)
    print(json.dumps(dict(snapshot=store.snapshot_id, candidates=candidates,
                         scope='publication only; every package must be checked before emission')))

if __name__ == '__main__': main()
