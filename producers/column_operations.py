"""Direct column mutation definitions and universal per-column preservation laws.

Translate each source table primitive literally. Columns are synchronized by the
encode relation, not by a sortedness or uniqueness assumption. Unsupported
primitive shapes fail authoring; supplied proof bytes always require checking.
"""
from action_replacement import var, call, cons, convert, trans
from point_delta import sub, choice, normal, equality
from representations import match


def prepare_operations(table, root_sort, cid, columns, selectors, components,
                       function, theorem, objects):
    operations, laws = {}, {}
    for operation in ['insert', 'remove', 'replace']:
        original = objects[table[operation]]['payload']['declaration']['Function']
        source_match = original['body'].get('Match', {})
        if source_match.get('scrutinee') != var(original['params'][0][0]):
            raise ValueError('direct column mutation needs an inductive primitive')
        empty, row = source_match['branches']
        old_key, old_row, old_tail = row['bindings']
        rest = original['params'][1:]
        args = [var(n) for n, _ in rest]
        per_column, proofs = [], []
        for index, column in enumerate(columns):
            def cell(row_value):
                if row_value == var(old_row):
                    return var('cell')
                if 'If' in row_value:
                    x = row_value['If']
                    return choice(sub(x['condition'], {old_key: var('head_key')}),
                                  cell(x['on_true']), cell(x['on_false']))
                return components(row_value)[index - 1]

            def project(term):
                if term == var(original['params'][0][0]):
                    return var('keys' if index == 0 else 'cells')
                if term == var(old_tail):
                    return var('tail_keys' if index == 0 else 'tail_cells')
                if 'Construct' in term and term['Construct']['datatype'] == table['datatype']:
                    x = term['Construct']
                    if x['constructor'] == 0:
                        return cons(column['Data'], 0, [])
                    key, value, tail = x['arguments']
                    head = sub(key, {old_key: var('head_key')}) if index == 0 else cell(value)
                    return cons(column['Data'], 1, [head, project(tail)])
                if 'SelfCall' in term:
                    tail, *extra = term['SelfCall']
                    if tail != var(old_tail):
                        raise ValueError('unsupported column primitive recursive root')
                    return {'SelfCall': [var('tail_keys'), *([] if index == 0 else [var('tail_cells')]),
                                         *[sub(a, {old_key: var('head_key')}) for a in extra]]}
                if 'If' in term:
                    x = term['If']
                    return choice(sub(x['condition'], {old_key: var('head_key')}),
                                  project(x['on_true']), project(x['on_false']))
                raise ValueError('unsupported column primitive root expression')

            empty_body = project(empty['body'])
            row_body = project(row['body'])
            params = [['keys', columns[0]], *([] if index == 0 else [['cells', column]]), *rest]
            if index:
                row_body = match(var('cells'), [([], cons(column['Data'], 0, [])),
                                 (['cell', 'tail_cells'], row_body)])
            body = match(var('keys'), [([], empty_body), (['head_key', 'tail_keys'], row_body)])
            physical = function(params, column, body, recursive=0)
            per_column.append(physical)
            source = lambda r: call(selectors[index], [call(table[operation], [r, *args])])
            direct = lambda r: call(physical, [call(selectors[0], [r]),
                                      *([] if index == 0 else [call(selectors[index], [r])]), *args])
            nil = cons(table['datatype'], 0, [])
            bound = cons(table['datatype'], 1, [var(old_key), var(old_row), var(old_tail)])
            # Every guard occurs in the source primitive and can be split using
            # ordinary Boolean elimination. No source key range is assumed.
            guards = []
            def collect(t):
                if isinstance(t, dict):
                    if 'If' in t and t['If']['condition'] not in guards:
                        guards.append(t['If']['condition'])
                    for v in t.values(): collect(v)
                elif isinstance(t, list):
                    for v in t: collect(v)
            collect(row['body'])
            def prove(a, b, level=0, facts=()):
                if level == len(guards):
                    return equality(a, b, objects,
                                    hyp=(direct(var(old_tail)), source(var(old_tail)), 0), facts=facts)
                guard = guards[level]
                return {'BoolSplit': dict(condition=guard, **{'from': a, 'to': b}, **{
                    label: prove(a, b, level + 1, (*facts, (guard, {'Bool': flag}, level + 1)))
                    for label, flag in [('on_false', False), ('on_true', True)]})}
            left, right = direct(var('rows')), source(var('rows'))
            proof = {'Induction': dict(variable='rows', **{'from': left, 'to': right}, cases=[
                dict(bindings=[], proof=convert(direct(nil), source(nil))),
                dict(bindings=[old_key, old_row, old_tail], proof=prove(direct(bound), source(bound)))])}
            proofs.append(theorem([['rows', root_sort], *rest], left, right, proof))
        names = ['mutation_column_' + str(i) for i in range(len(columns))]
        physical = function([['columns', {'Data': cid}], *rest], {'Data': cid},
            match(var('columns'), [(names, cons(cid, 0, [call(f, [var(names[0]),
                *([] if i == 0 else [var(names[i])]), *args]) for i, f in enumerate(per_column)]))]))
        operations[operation] = physical
        # Factoring each column's induction keeps the combined law bounded.
        direct = call(physical, [cons(cid, 0, [call(f, [var('rows')]) for f in selectors]), *args])
        projected = cons(cid, 0, [call(f, [call(table[operation], [var('rows'), *args])]) for f in selectors])
        laws[operation] = theorem([['rows', root_sort], *rest], direct, projected,
            trans(convert(direct, cons(cid, 0, [call(f, [call(selectors[0], [var('rows')]),
                *([] if i == 0 else [call(selectors[i], [var('rows')])]), *args]) for i, f in enumerate(per_column)])),
                {'Construct': dict(datatype=cid, constructor=0, arguments=[
                    {'Use': dict(theorem=p, arguments=[var('rows'), *args], premises=[])} for p in proofs])}))
    return operations, laws
