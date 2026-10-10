#!/usr/bin/env python3
"""Untrusted producer: prove that a maintained view equals its row decomposition.

Input is the compiler's `ink model-view` output for one `keep`:
literal stage list functions for a `sum`/`count` over any chain of
`map`/`filter` stages, the final fold, `pipeline(rows)` and
`decomposed(rows) = Σ projection(row)`. Output is `ink verify-view` evidence:
the same bundle plus lemmas, and a proof of

    ∀ rows. pipeline(rows) = decomposed(rows)

The proof is generic: it never inspects what a lambda computes, only the
stage structure the compiler exported, so it works for every program in the
supported pipeline subset. For stage k with element sort E_k it defines

    proj_k(head)  = proj_{k+1}(f_k(head))            (map f_k)
                  = if p_k(head) then proj_{k+1}(head) else 0   (filter p_k)
    proj_{n+1}(head) = head (sum) | 1 (count)
    sp_k(xs)      = Σ_{x ∈ xs} proj_k(x)

and proves, by one induction each (filters use one Boolean case split):

    S_k : sp_{k+1}(stage_k(xs)) = sp_k(xs)
    F   : fold(xs) = sp_{n+1}(xs)
    D   : sp_1(rows) = decomposed(rows)        (projections agree by computation)

then chains them. The compiler checks every object and the final proof with
its unchanged general kernel; nothing here is trusted.
"""
import argparse, copy, hashlib, json, sys
from pathlib import Path

SEMANTICS = 'first-order-inductive-equality-v1'
VIEW_SEMANTICS = 'source-view-pipeline-decomposition-v1'


def var(n): return {'Var': n}
def call(f, *args): return {'Call': {'function': f, 'arguments': list(args)}}
def construct(d, i, *args): return {'Construct': {'datatype': d, 'constructor': i, 'arguments': list(args)}}
def refl(t): return {'Refl': t}
def hyp(i): return {'Hypothesis': i}
def sym(p): return {'Sym': p}
def congruence(f, *proofs): return {'Call': {'function': f, 'arguments': list(proofs)}}
def use(theorem, *args): return {'Use': {'theorem': theorem, 'arguments': list(args), 'premises': []}}
def list_match(scrutinee, nil, cons):
    return {'Match': {'scrutinee': var(scrutinee), 'branches': [
        {'bindings': [], 'body': nil}, {'bindings': ['head', 'tail'], 'body': cons}]}}
def induction(variable, left, right, nil_proof, cons_proof):
    return {'Induction': {'variable': variable, 'from': left, 'to': right, 'cases': [
        {'bindings': [], 'proof': nil_proof}, {'bindings': ['head', 'tail'], 'proof': cons_proof}]}}


def trans(proofs):
    """Balanced transitivity keeps proof depth logarithmic in chain length."""
    if len(proofs) == 1:
        return proofs[0]
    mid = len(proofs) // 2
    return {'Trans': [trans(proofs[:mid]), trans(proofs[mid:])]}


def references(value):
    out = set()
    if isinstance(value, list):
        for v in value:
            out |= references(v)
    elif isinstance(value, dict):
        for k, v in value.items():
            if k in ('datatype', 'function', 'theorem') and isinstance(v, str):
                out.add(v)
            if k == 'Data' and isinstance(v, str):
                out.add(v)
            out |= references(v)
    return out


def produce(view):
    description = view['description']
    bundle = copy.deepcopy(view['library'])
    objects, lock = bundle['objects'], bundle['lock']['objects']
    decl = lambda ident: json.loads(objects[ident])['declaration']

    # Field matches inside translated lambdas can reach nested record sorts
    # that no explicit reference names; import every source value sort.
    value_sorts = {v['Data'] for v in description['row']['types'].values() if isinstance(v, dict) and 'Data' in v}

    def store(name, kind, declaration, extra=()):
        deps = sorted(references(declaration) | set(extra) | (value_sorts if kind != 'Datatype' else set()))
        raw = json.dumps({'schema': 1, 'semantics': SEMANTICS, 'name': name,
                          'dependencies': deps, 'declaration': {kind: declaration}},
                         separators=(',', ':'))
        ident = hashlib.sha256(raw.encode()).hexdigest()
        if ident not in objects:
            objects[ident] = raw
            lock.append(ident)
        return ident

    keep = description['row']['keep']
    fold = decl(description['fold'])['Function']
    integer = fold['result']['Data']
    # Exact-integer constants and addition are read from the exported fold:
    # Nil -> 0, Cons -> add(fold(tail), item).
    zero = fold['body']['Match']['branches'][0]['body']
    addition = fold['body']['Match']['branches'][1]['body']['Call']['function']
    natural = decl(integer)['Datatype']['constructors'][1]['fields'][0]['Data']
    one = construct(integer, 1, construct(natural, 0))
    add = lambda a, b: call(addition, a, b)

    stages = description['stages']
    sorts = [description['rows']] + [s['output'] for s in stages]   # L_1 .. L_{n+1}
    element = lambda list_sort: decl(list_sort['Data'])['Datatype']['constructors'][1]['fields'][0]
    n = len(stages)

    # proj_{n+1} .. proj_1 (built from the end), then sp_k for each k.
    proj = [None] * (n + 2)
    proj[n + 1] = store(f'view_{keep}_proj_{n + 1}', 'Function', {
        'params': [['head', element(sorts[n])]], 'result': {'Data': integer},
        'body': var('head') if description['aggregate'] == 'sum' else one, 'recursive': None})
    stage_terms = []
    for k in range(n, 0, -1):
        stage = stages[k - 1]
        body = decl(stage['function'])['Function']['body']['Match']['branches'][1]['body']
        if stage['kind'] == 'map':
            term = body['Construct']['arguments'][0]
            proj_body = call(proj[k + 1], term)
        else:
            term = body['If']['condition']
            proj_body = {'If': {'condition': term, 'on_true': call(proj[k + 1], var('head')), 'on_false': zero}}
        stage_terms.insert(0, term)
        proj[k] = store(f'view_{keep}_proj_{k}', 'Function', {
            'params': [['head', element(sorts[k - 1])]], 'result': {'Data': integer},
            'body': proj_body, 'recursive': None})
    sp = [None] * (n + 2)
    for k in range(1, n + 2):
        sp[k] = store(f'view_{keep}_sum_proj_{k}', 'Function', {
            'params': [['xs', sorts[k - 1]]], 'result': {'Data': integer},
            'body': list_match('xs', zero, add({'SelfCall': [var('tail')]}, call(proj[k], var('head')))),
            'recursive': 0})

    nat_int = {natural, integer}

    def theorem(name, params, left, right, proof):
        return store(name, 'Theorem', {'params': params, 'conditions': [], 'from': left, 'to': right,
                                       'proof': proof}, extra=nat_int)

    xs, head, tail = var('xs'), var('head'), var('tail')
    lemmas = [None] * (n + 1)
    for k in range(1, n + 1):
        stage = stages[k - 1]
        f = stage['function']
        left, right = call(sp[k + 1], call(f, xs)), call(sp[k], xs)
        if stage['kind'] == 'map':
            step = congruence(addition, hyp(0), refl(call(proj[k + 1], stage_terms[k - 1])))
        else:
            hole = 'view_condition'
            c = var(hole)
            lhs = call(sp[k + 1], {'If': {'condition': c,
                                          'on_true': construct(sorts[k - 1]['Data'], 1, head, call(f, tail)),
                                          'on_false': call(f, tail)}})
            rhs = add(call(sp[k], tail), {'If': {'condition': c, 'on_true': call(proj[k + 1], head), 'on_false': zero}})
            fix = lambda context: {'Substitute': {'variable': hole, 'context': context, 'equality': hyp(1)}}
            kept = trans([fix(lhs), congruence(addition, hyp(0), refl(call(proj[k + 1], head))), sym(fix(rhs))])
            dropped = trans([fix(lhs), hyp(0), sym(fix(rhs))])
            cons = construct(sorts[k - 1]['Data'], 1, head, tail)
            step = {'BoolSplit': {'condition': stage_terms[k - 1],
                                  'from': call(sp[k + 1], call(f, cons)), 'to': call(sp[k], cons),
                                  'on_false': dropped, 'on_true': kept}}
        lemmas[k] = theorem(f'view_{keep}_stage_{k}_decomposes', [['xs', sorts[k - 1]]], left, right,
                            induction('xs', left, right, refl(zero), step))
    left, right = call(description['fold'], xs), call(sp[n + 1], xs)
    fold_lemma = theorem(f'view_{keep}_fold_decomposes', [['xs', sorts[n]]], left, right,
                         induction('xs', left, right, refl(zero),
                                   congruence(addition, hyp(0), refl(call(proj[n + 1], head)))))
    rows = var('rows')
    left, right = call(sp[1], rows), call(description['decomposed'], rows)
    projection = description['row']['projection']
    agree = {'Convert': {'from': call(proj[1], head), 'to': call(projection, head)}}
    rows_lemma = theorem(f'view_{keep}_projection_agrees', [['rows', sorts[0]]], left, right,
                         {'Induction': {'variable': 'rows', 'from': left, 'to': right, 'cases': [
                             {'bindings': [], 'proof': refl(zero)},
                             {'bindings': ['head', 'tail'], 'proof': congruence(addition, hyp(0), agree)}]}})

    # pipeline(rows) = fold(inner_n) = sp_{n+1}(inner_n) = sp_n(inner_{n-1}) = ... = sp_1(rows) = decomposed(rows)
    inner = [rows]
    for stage in stages:
        inner.append(call(stage['function'], inner[-1]))
    chain = [use(fold_lemma, inner[n])] + [use(lemmas[k], inner[k - 1]) for k in range(n, 0, -1)] + [use(rows_lemma, rows)]
    return {'schema': 1, 'semantics': VIEW_SEMANTICS, 'keep': keep, 'library': bundle, 'proof': trans(chain)}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('view', type=Path, help='ink model-view output')
    parser.add_argument('-o', '--output', type=Path, required=True)
    args = parser.parse_args()
    view = json.loads(args.view.read_text())
    if view['description'].get('semantics') != VIEW_SEMANTICS:
        sys.exit('unsupported view model semantics')
    args.output.write_text(json.dumps(produce(view), separators=(',', ':')))
    print(f'wrote {args.output}; the compiler must check it with verify-view')


if __name__ == '__main__':
    main()
