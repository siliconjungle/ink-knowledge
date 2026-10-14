"""Stored, untrusted word equivalences; ordinary source-law admission is mandatory.

No solver or target recogniser runs during compilation. Matching only limits
proposals; every reconstructed circuit and certificate must replay in core.
"""
import gzip,json
from importlib.resources import files

def specialize(subject,core):
    from ink_planner.semantic_search import positions,match
    rows=json.loads(gzip.decompress(files('producers').joinpath('data/source-word-laws.json.gz').read_bytes()))
    sites=[term for body in subject.get('functions',{}).values() for _,term in positions(body)]
    return [('word_'+row['name'],row['law']) for row in rows
            if any(match(row['law']['from'],site,row['law']['params'],{}) for site in sites)]
