"""Untrusted authoring with explicit, proved scalar equalities.

The author may use the supplied equalities while searching. Each is discharged
by ordinary AssertEquality/Congruence replay, under the original conditions and
earlier equalities. This adds no inference rule, trusted fact or admission path.
"""
import copy
from .semantic_laws import law, op, value


def prove_with_equalities(goal, facts, author, *, dependencies=()):
    """Ask ``author`` for a proof of a strengthened goal, then discharge facts.

    Facts are endpoint/proof triples in the goal's lexical environment. Their
    proofs must establish the exact endpoints; the compiler checks this again.
    The caller supplies any external proof dependencies explicitly. Inlining a
    self-contained witness needs none and preserves ordinary frozen discovery.
    """
    if (not facts or len(facts) > 16 or
            len(goal['conditions']) + len(facts) > 128):
        raise ValueError('bounded equality assistance required')
    equations = []
    for fact in facts:
        if set(fact) != {'from', 'to', 'proof'}:
            raise ValueError('explicit equality endpoints and proof required')
        sort = fact['from']['sort']
        if (sort != fact['to']['sort'] or
                sort not in [value(t) for t in ['U32', 'U64', 'I32', 'Bool']]):
            raise ValueError('exact word or Boolean equality required')
        equations.append({k: copy.deepcopy(fact[k]) for k in ['from', 'to']})
    request = copy.deepcopy(goal)
    request['conditions'].extend(equations)
    proof = author(request)
    for fact, equation in reversed(list(zip(facts, equations))):
        # Reflect a proved exact scalar equality into its Boolean proposition;
        # AssertEquality itself accepts that proposition, not an unproved fact.
        middle = op(value('Bool'), 'binary:==', equation['to'], equation['to'])
        premise = {'Trans': dict(middle=middle,
            left={'Congruence': [copy.deepcopy(fact['proof']), 'Normalize']},
            right='Normalize')}
        proof = {'AssertEquality': dict(equality=equation,
            premise=premise, body=proof)}
    return law(goal['params'], goal['from'], goal['to'], proof,
               conditions=goal['conditions'], dependencies=dependencies)
