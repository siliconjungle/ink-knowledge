"""Reusable observation laws from checked, scoped source equations.

No property, datatype or compiler-strategy names are recognized. The source
checker establishes applicability; this producer only proposes ordinary laws
whose premises are those same equations. Its normalisation is untrusted.
"""
import copy
from .beta_specialization15 import beta_normalize


def specialize(subject, core):
    from ink_planner.semantic_search import children
    from .definition_context28 import bind
    from .contract_proofs import context_for
    rows = []
    seen = set()
    import json
    for function, sites in subject.get('contexts', {}).items():
        for site in sites:
            for equation in site['conditions']:
                original = copy.deepcopy(equation['from'])
                target = copy.deepcopy(equation['to'])
                source = beta_normalize(copy.deepcopy(original))
                if source == target:
                    continue
                free = set()
                def visit(term, depth=0, binders=0):
                    if depth > 128:
                        raise ValueError('established fact term depth')
                    node = term['node']
                    if isinstance(node, dict) and 'Free' in node:
                        free.add(node['Free'])
                    if isinstance(node, dict) and 'Bound' in node and node['Bound'] >= binders:
                        raise ValueError('established fact escapes source scope')
                    for child in children(term):
                        visit(child, depth + 1, binders + int(isinstance(node,dict) and 'Lambda' in node))
                try:
                    visit(original); visit(target)
                except ValueError:
                    continue
                if source['sort'] != target['sort']:
                    continue
                if not free.issubset(site['parameters']):
                    continue
                proposal = dict(semantics='ink-conditional-laws-v1',
                    params={name:site['parameters'][name] for name in sorted(free)},
                    conditions=[copy.deepcopy(equation)],
                    **{'from':source, 'to':target},
                    proof={'Trans':dict(middle=original,left='Normalize',right={'Hypothesis':0})},
                    dependencies=[])
                proposal = bind(proposal, core, subject)
                # Only reachable schemas/definitions belong to a reusable law.
                # Unrelated module declarations must not prevent its reuse.
                proposal['definition_context'] = context_for(proposal['definition_context'], proposal)
                key = json.dumps(proposal, sort_keys=True)
                if key in seen:
                    continue
                seen.add(key)
                rows.append(('established-fact/'+function+'/'+str(len(rows)), proposal))
                if len(rows) >= 256:
                    return rows
    return rows
