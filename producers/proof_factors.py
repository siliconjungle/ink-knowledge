"""Bound proof-checking work by publishing ordinary intermediate lemmas.

Endpoints are authoring calculations, never checking authority. Every lemma and
use remains subject to the same general checker and unchanged resource limits.
"""
from point_delta import sub
from action_replacement import cons


def equation(proof, objects, conditions):
    if 'Convert' in proof:
        p=proof['Convert'];return p['from'],p['to']
    if 'Refl' in proof:return proof['Refl'],proof['Refl']
    if 'Hypothesis' in proof:
        p=conditions[proof['Hypothesis']];return p['from'],p['to']
    if 'Use' in proof:
        p=proof['Use'];decl=objects[p['theorem']]['payload']['declaration']['Theorem']
        mapping=dict(zip([n for n,_ in decl['params']],p['arguments']))
        return sub(decl['from'],mapping),sub(decl['to'],mapping)
    if 'Sym' in proof:
        a,z=equation(proof['Sym'],objects,conditions);return z,a
    if 'Trans' in proof:return equation(proof['Trans'][0],objects,conditions)[0],equation(proof['Trans'][-1],objects,conditions)[1]
    if 'Substitute' in proof:
        p=proof['Substitute'];a,z=equation(p['equality'],objects,conditions)
        return sub(p['context'],{p['variable']:a}),sub(p['context'],{p['variable']:z})
    for name in ['BoolSplit','Induction','BitVector','WordExtensionality']:
        if name in proof:return proof[name]['from'],proof[name]['to']
    if 'Construct' in proof:
        p=proof['Construct'];parts=[equation(q,objects,conditions)for q in p['arguments']]
        return tuple(cons(p['datatype'],p['constructor'],[x[i]for x in parts])for i in [0,1])
    if 'Binary' in proof:
        p=proof['Binary'];a,z=equation(p['left'],objects,conditions),equation(p['right'],objects,conditions)
        return tuple({'Binary':dict(op=p['op'],left=a[i],right=z[i])}for i in [0,1])
    raise ValueError('unsupported proof factor '+str(list(proof)))
