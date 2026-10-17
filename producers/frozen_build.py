#!/usr/bin/env python3
"""Explicit frozen-build authoring: closed traversal composition or direct proof.

This selects a bounded proof-construction strategy, not an automatically
profitable implementation. Both producers replay the complete result before
publication; failure in a chosen strategy is reported without silently falling
back to an unchecked or different proposal.
"""
import json
from pathlib import Path
import sys
import subprocess

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from producers import frozen_composition, frozen_specialization


def main():
    # Both producers expose the same input/--ink/-o interface. Parse it once to
    # apply the same source byte bound before inspecting the opportunity.
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--ink', required=True, type=Path)
    parser.add_argument('-o', '--output', required=True, type=Path)
    args = parser.parse_args()
    if args.source.stat().st_size > 16_000_000:
        raise ValueError('frozen build source byte limit')
    from producers.closed_reference_calls import ReferenceCalls
    _, helpers = frozen_composition.propose_source(json.loads(args.source.read_bytes()),
                                                 closed_call=ReferenceCalls(args.source, args.ink))
    (frozen_composition if helpers else frozen_specialization).main()


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.exit(error.stderr.decode(errors='replace').strip() or 'compiler rejected frozen specialization')
