"""Replayable general word equality extraction, with a locally replayable bit-vector proof."""
import json, subprocess, tempfile
from pathlib import Path
from producers.action_replacement import var
from producers.point_delta import binary


def word_equality(add, compiler):
    a,b=var('equal_a'),var('equal_b')
    goal=dict(params=[['equal_a','U64'],['equal_b','U64']],conditions=[{'from':binary('==',a,b),'to':{'Bool':True}}],**{'from':a,'to':b})
    frozen=Path(__file__).resolve().parent/'data/word-equality.json'
    if frozen.exists():
        declaration=json.loads(frozen.read_text())
        if {k:declaration['Theorem'][k] for k in goal}!=goal:raise ValueError('word equality proposal differs from its statement')
        return add(declaration)
    with tempfile.TemporaryDirectory(prefix='ink-word-equality-') as directory:
        path=Path(directory);(path/'goal.json').write_text(json.dumps(goal))
        subprocess.run([str(compiler),'bitvector-obligation',str(path/'goal.json'),'-o',str(path/'cnf.json')],check=True,capture_output=True)
        problem=json.loads((path/'cnf.json').read_text())
    from producers.bitvector_proofs import certificate
    proof=certificate(problem)
    declaration={'Theorem':dict(**goal,proof={'BitVector':dict(**{'from':a,'to':b},hypotheses=[0],certificate=proof)})}
    return add(declaration)
