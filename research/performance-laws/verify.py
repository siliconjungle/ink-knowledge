#!/usr/bin/env python3
"""Reproduce proof admission/replay evidence; never benchmark or publish production."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
KNOWLEDGE = ROOT.parents[1]
sys.path.insert(0, str(KNOWLEDGE))
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.performance_laws import named_laws, publish
from tests.test_performance_laws import SOURCE


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, default=KNOWLEDGE.parent / 'target/release/ink')
    args = parser.parse_args()
    compiler = args.compiler.resolve()
    _, manifest = publish(ROOT)
    source, core, selection = ROOT / 'validation.ink', ROOT / 'validation.core.json', ROOT / 'validation.selection.json'
    source.write_text(SOURCE)
    def run(*command):
        return subprocess.run(command, check=True, capture_output=True, text=True)
    run(compiler, 'emit-core', source, '-o', core)
    accepted = run(compiler, 'knowledge-check', core, ROOT / 'view.json')
    planner = run(sys.executable, KNOWLEDGE.parent / 'planner/plan.py', '--compiler', compiler,
                  '--core', core, '--snapshot', ROOT / 'store/snapshot.json', '--budget', '4096', '-o', selection)
    replay = run(compiler, 'check-selection', core, selection)
    proofs = dict(named_laws())
    false = copy.deepcopy(proofs['zero_sum_u32'])
    false['to']['node']['Word'] = 1
    naked = copy.deepcopy(proofs['repeat_subtract_u32'])
    naked['proof'] = 'Normalize'
    rejected = {}
    for name, candidate in [('wrong-result', false), ('missing-induction', naked)]:
        with tempfile.TemporaryDirectory() as temp:
            obj = semantic_entry(candidate)
            store = Store.publish(Path(temp), [obj])
            view = ROOT / f'{name}.view.json'
            view.write_bytes(canonical(store.bundle([identity(obj)])) + b'\n')
            result = subprocess.run([compiler, 'knowledge-check', core, view], capture_output=True, text=True)
            if result.returncode == 0 or 'semantic normal forms differ' not in result.stderr:
                raise RuntimeError('forged proof did not receive the expected semantic rejection')
            rejected[name] = dict(exit_code=result.returncode, error=result.stderr.strip(), hash_valid=True)
    package = json.loads(selection.read_text())
    names = {i: n for n, i in manifest['names'].items()}
    report = dict(schema=1, compiler_sha256=hashlib.sha256(compiler.read_bytes()).hexdigest(),
                  proof_check=json.loads(accepted.stdout), planner=json.loads(planner.stdout),
                  selection_replay=json.loads(replay.stdout),
                  selected_names=[names[a['law']] for a in package['applications']],
                  forged_proof_rejections=rejected, timed_benchmarks=False)
    (ROOT / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(accepted_laws=len(report['proof_check']['entries']),
                         selected_names=report['selected_names'], rejected=rejected)))


if __name__ == '__main__':
    main()
