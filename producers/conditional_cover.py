"""Propose a bounded Boolean case tree from conditional bitvector witnesses.

This is ordinary authoring, not cover/admission authority. The existing Cases
checker must replay every leaf under the complete shared semantic/RUP budgets.
"""
import copy
from ink_knowledge import canonical
from .rup_transport import pack_certificate


def boolean_cover(laws, *, maximum_depth=16, maximum_leaves=64, pack_hints=False):
    if not laws or len(laws) > 64 or type(maximum_depth) is not int or not 1 <= maximum_depth <= 16 or type(maximum_leaves) is not int or not 1 <= maximum_leaves <= 64:
        raise ValueError('bounded Boolean cover inputs required')
    def statement(law):
        return {k: v for k, v in law.items() if k not in {'conditions', 'proof', 'dependencies'}}
    shape = statement(laws[0])
    candidates = []
    for law in laws:
        if statement(law) != shape or set(law['proof']) != {'BitVector'} or len(law['conditions']) > 128:
            raise ValueError('matching statements and explicit bitvector witnesses required')
        premises = []
        for equation in law['conditions']:
            flag = equation.get('to', {}).get('node', {}).get('Bool')
            if type(flag) is not bool or equation['from']['sort'] != {'Value':'Bool'} or equation['to']['sort'] != {'Value':'Bool'}:
                raise ValueError('Boolean equations required')
            premises.append((canonical(equation['from']), flag))
        indices = law['proof']['BitVector']['hypotheses']
        if any(type(i) is not int or not 0 <= i < len(premises) for i in indices):
            raise ValueError('explicit local premise indices required')
        candidates.append((law, premises))
    leaves = 0
    def tree(facts, available):
        nonlocal leaves
        known = dict(facts)
        compatible = []
        for law, premises in available:
            if any(term in known and known[term] != flag for term, flag in premises):
                continue
            missing = [pair for pair in premises if pair[0] not in known]
            if not missing:
                leaves += 1
                if leaves > maximum_leaves:
                    raise ValueError('Boolean cover leaf limit')
                body = copy.deepcopy(law['proof']['BitVector'])
                body['hypotheses'] = [facts.index(premises[i]) for i in body['hypotheses']]
                if pack_hints:
                    body['certificate'] = pack_certificate(body['certificate'])
                return {'BitVector': body}
            compatible.append((law, premises, missing))
        if not compatible:
            raise ValueError('conditional proofs do not cover this Boolean branch')
        if len(facts) >= maximum_depth:
            raise ValueError('Boolean cover depth limit')
        # Policy only: expose a shortest remaining premise before duplicating a
        # larger witness. Reconstructing the complete tree remains mandatory.
        chosen = min(compatible, key=lambda row: len(row[2]))
        term, _ = chosen[2][0]
        condition = next(e['from'] for e in chosen[0]['conditions'] if canonical(e['from']) == term)
        rows = [(law, premises) for law, premises, _ in compatible]
        return {'Cases':dict(condition=copy.deepcopy(condition),
            on_false=tree(facts + [(term, False)], rows),
            on_true=tree(facts + [(term, True)], rows))}
    result = copy.deepcopy(shape)
    result.update(conditions=[], dependencies=sorted({i for law in laws for i in law['dependencies']}), proof=tree([], candidates))
    return result
