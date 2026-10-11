"""Untrusted column layouts expressed as ordinary inductive definitions.

Keys and record fields use separate lists. Universal round trips include empty,
duplicate and unordered logical rows; equal column lengths follow from encode.
Mutations still decode/reencode ordinary source transitions. Optional point-read
induction proofs permit direct column search; emitted query erasure can remove
the unused logical state. No producer grants trusted native storage authority.
"""
from action_replacement import var, call, cons, convert, trans
from representations import match
from point_delta import binary, choice


def prepare(model, objects, add, packed_booleans=False, point_queries=False, mutations=False, ordered_queries=(), indexed=False, dense_slots=0):
    def scalar(left, right, params):
        import json, os, subprocess, tempfile
        from pathlib import Path
        from bitvector_proofs import certificate
        compiler = Path(os.environ.get('INK_COMPILER', 'target/debug/ink')).resolve()
        with tempfile.TemporaryDirectory(prefix='ink-column-proof-') as output:
            path = Path(output)
            (path / 'goal.json').write_text(json.dumps(dict(params=params, conditions=[], **{'from': left, 'to': right})))
            result = subprocess.run([str(compiler), 'bitvector-obligation', str(path / 'goal.json'), '-o', str(path / 'cnf.json')], capture_output=True, text=True)
            if result.returncode:
                raise ValueError(result.stderr)
            return {'BitVector': dict(**{'from': left, 'to': right}, hypotheses=[],
                                      certificate=certificate(json.loads((path / 'cnf.json').read_text())))}
    def datatype(constructors):
        return add({'Datatype': dict(constructors=constructors)})

    def function(params, result, body, recursive=None):
        return add({'Function': dict(params=params, result=result, body=body, recursive=recursive)})

    def theorem(params, left, right, proof, conditions=()):
        return add({'Theorem': dict(params=params, conditions=list(conditions), **{'from': left, 'to': right}, proof=proof)},
                   [k for k, v in objects.items() if 'Datatype' in v['payload'].get('declaration', {})])

    def sequence(sort):
        key = datatype([dict(name='ColumnNil', fields=[]), dict(name='ColumnCons', fields=[sort, 'SelfType'])])
        return {'Data': key}

    def use(key, arguments):
        return {'Use': dict(theorem=key, arguments=arguments, premises=[])}

    physical, encodes, decodes, roundtrips = [], [], [], []
    point_functions, point_laws = [], []
    operation_functions, operation_laws = [], []
    ordered_functions, ordered_laws = {}, {}
    logical_fields = objects[model['state']]['payload']['declaration']['Datatype']['constructors'][0]['fields']
    if len(logical_fields) != len(model['tables']):
        raise ValueError('column producer needs one logical root per table')
    for table, root_sort in zip(model['tables'], logical_fields):
        if root_sort != {'Data': table['datatype']}:
            raise ValueError('column producer table/root order mismatch')
        table_fields = objects[table['datatype']]['payload']['declaration']['Datatype']['constructors'][1]['fields']
        row_sort = table_fields[1]
        row_fields = [row_sort]
        row_id = None
        # Source records are one-constructor data. Other values stay as a single
        # column, including Option/enums, lists, Strings and exact integers.
        if isinstance(row_sort, dict) and 'Data' in row_sort and len(objects[row_sort['Data']]['payload']['declaration']['Datatype']['constructors']) == 1:
            row_id = row_sort['Data']
            row_fields = objects[row_id]['payload']['declaration']['Datatype']['constructors'][0]['fields']
        if len(row_fields) > 16:
            raise ValueError('column producer record width budget')
        key_sort = table_fields[0]
        bool_fields = [i for i, sort in enumerate(row_fields) if sort == 'Bool'] if packed_booleans and row_id else []
        plain_fields = [i for i in range(len(row_fields)) if i not in bool_fields]
        payload_sorts = [row_fields[i] for i in plain_fields] + (['U64'] if bool_fields else [])
        view_specs=[]
        if ordered_queries:
            if len(model['tables'])!=1:raise ValueError('ordered column authoring currently needs one table')
            from ordered_columns import contribution
            for query_name in ordered_queries:
                view_specs.append((query_name,*contribution(model,query_name,table,row_sort,function,objects)))
        sorts = [key_sort, *payload_sorts, *[v[1]for v in view_specs]]
        columns = [sequence(sort) for sort in sorts]
        cid = datatype([dict(name='Columns', fields=columns)])
        column_sort = {'Data': cid}
        physical.append(column_sort)
        getters = []
        def pack(values):
            result = {'U64': 0}
            for bit, index in enumerate(bool_fields):
                result = binary('+', result, choice(values[index], {'U64': 1 << bit}, {'U64': 0}))
            return result

        def components(row):
            values = [call(g, [row]) for g in getters] if row_id else [row]
            return [values[i] for i in plain_fields] + ([pack(values)] if bool_fields else []) + [call(spec[2],[row])for spec in view_specs]

        def restore(values):
            if not row_id:
                return values[0]
            fields = [None] * len(row_fields)
            for i, value in zip(plain_fields, values):
                fields[i] = value
            for bit, i in enumerate(bool_fields):
                fields[i] = binary('!=', binary('&', values[len(plain_fields)], {'U64': 1 << bit}), {'U64': 0})
            return cons(row_id, 0, fields)

        if row_id:
            fields = ['column_field_' + str(i) for i in range(len(row_fields))]
            getters = [function([['row', row_sort]], sort,
                                match(var('row'), [(fields, var(fields[i]))]), recursive=0)
                       for i, sort in enumerate(row_fields)]
            eta_left = restore(components(var('row')))
            bound = cons(row_id, 0, [var(n) for n in fields])
            eta_case = convert(restore(components(bound)), bound)
            if bool_fields:
                values = [var(n) for n in fields]
                restored = restore([values[i] for i in plain_fields] + [pack(values)])
                params = [[fields[i], 'Bool'] for i in bool_fields]
                parts = [scalar(restored['Construct']['arguments'][i], values[i], params) if i in bool_fields else {'Refl': values[i]}
                         for i in range(len(fields))]
                eta_case = trans(convert(restore(components(bound)), restored),
                                 {'Construct': dict(datatype=row_id, constructor=0, arguments=parts)})
            eta = theorem([['row', row_sort]], eta_left, var('row'),
                          {'Induction': dict(variable='row', **{'from': eta_left, 'to': var('row')},
                                             cases=[dict(bindings=fields,
                                                         proof=eta_case)])})
        selectors = []
        for i, output in enumerate(columns):
            head = var('key') if i == 0 else components(var('row'))[i-1]
            selectors.append(function([['rows', root_sort]], output,
                match(var('rows'), [([], cons(output['Data'], 0, [])),
                    (['key', 'row', 'tail'], cons(output['Data'], 1, [head, {'SelfCall': [var('tail')]}]))]), recursive=0))
        encode = function([['rows', root_sort]], column_sort,
                          cons(cid, 0, [call(f, [var('rows')]) for f in selectors]))
        params = [['column_' + str(i), sort] for i, sort in enumerate(columns)]
        heads = [var('head_' + str(i)) for i in range(len(columns))]
        tails = [var('tail_' + str(i)) for i in range(len(columns))]
        restored_row = restore(heads[1:])
        zipped = cons(table['datatype'], 1, [heads[0], restored_row, {'SelfCall': tails}])
        for i in reversed(range(len(columns))):
            zipped = match(var(params[i][0]), [([], cons(table['datatype'], 0, [])),
                           (['head_' + str(i), 'tail_' + str(i)], zipped)])
        zipper = function(params, root_sort, zipped, recursive=0)
        names = [p[0] for p in params]
        decode = function([['columns', column_sort]], root_sort,
                          match(var('columns'), [(names, call(zipper, [var(n) for n in names]))]))
        encodes.append(encode)
        decodes.append(decode)
        rows = var('rows')
        left = call(decode, [call(encode, [rows])])
        nil = cons(table['datatype'], 0, [])
        bound = cons(table['datatype'], 1, [var('key'), var('row'), var('tail')])
        rebuilt = restore(components(var('row')))
        recursive = call(decode, [call(encode, [var('tail')])])
        middle = cons(table['datatype'], 1, [var('key'), rebuilt, recursive])
        row_proof = use(eta, [var('row')]) if row_id else {'Refl': var('row')}
        step = trans(convert(call(decode, [call(encode, [bound])]), middle),
                     {'Construct': dict(datatype=table['datatype'], constructor=1,
                                        arguments=[{'Refl': var('key')}, row_proof, {'Hypothesis': 0}])})
        roundtrips.append(theorem([['rows', root_sort]], left, rows,
                          {'Induction': dict(variable='rows', **{'from': left, 'to': rows},
                            cases=[dict(bindings=[], proof=convert(call(decode, [call(encode, [nil])]), nil)),
                                   dict(bindings=['key', 'row', 'tail'], proof=step)])}))
        if view_specs:
            from ordered_columns import prove_read
            for vi,(query_name,result,mapper,query)in enumerate(view_specs):
                index=1+len(payload_sorts)+vi
                ordered_functions[query_name],ordered_laws[query_name]=prove_read(table,root_sort,cid,columns,index,selectors[index],mapper,result,query,function,theorem,objects)
        if mutations:
            from column_operations import prepare_operations
            operations, laws = prepare_operations(table, root_sort, cid, columns, selectors, components, function, theorem, objects)
            operation_functions.append(operations)
            operation_laws.append(laws)
        if point_queries:
            from point_delta import sub, equality, normal, replace
            get = objects[table['get']]['payload']['declaration']['Function']
            source_match = get['body'].get('Match', {})
            if source_match.get('scrutinee') != var(get['params'][0][0]) or len(source_match.get('branches', [])) != 2:
                raise ValueError('column point search needs an inductive table get')
            empty_case, row_case = source_match['branches']
            if len(row_case['bindings']) != 3 or 'If' not in row_case['body']:
                raise ValueError('column point search needs a guarded table get')
            key_name = 'column_query_key'
            names_map = dict(zip(row_case['bindings'], [heads[0], restored_row, tails[0]]))
            names_map[get['params'][1][0]] = var(key_name)
            body = sub(row_case['body'], names_map)
            def recursive_calls(t):
                if isinstance(t, dict):
                    if 'SelfCall' in t:
                        if t['SelfCall'] != [tails[0], var(key_name)]:
                            raise ValueError('column point search changed recursive key')
                        return {'SelfCall': [*tails, var(key_name)]}
                    return {k: recursive_calls(v) for k, v in t.items()}
                if isinstance(t, list):
                    return [recursive_calls(v) for v in t]
                return t
            body = recursive_calls(body)
            empty_body = sub(empty_case['body'], {get['params'][1][0]: var(key_name)})
            for i in reversed(range(len(columns))):
                body = match(var(params[i][0]), [([], empty_body),
                             (['head_' + str(i), 'tail_' + str(i)], body)])
            search = function([*params, [key_name, key_sort]], get['result'], body, recursive=0)
            point = function([['columns', column_sort], [key_name, key_sort]], get['result'],
                             match(var('columns'), [(names, call(search, [*[var(n) for n in names], var(key_name)]))]))
            point_functions.append(point)
            query_key = var('query_key')
            point_on = lambda value: call(point, [call(encode, [value]), query_key])
            source_on = lambda value: call(table['get'], [value, query_key])
            guard = sub(row_case['body']['If']['condition'],
                        dict(zip(row_case['bindings'], [var('key'), var('row'), var('tail')])) |
                        {get['params'][1][0]: query_key})
            facts = [] if not row_id else [(normal(rebuilt, objects), var('row'), use(eta, [var('row')]))]
            cases = {}
            for label, value in [('on_false', False), ('on_true', True)]:
                cases[label] = equality(point_on(bound), source_on(bound), objects,
                    hyp=(point_on(var('tail')), source_on(var('tail')), 0),
                    facts=[(guard, {'Bool': value}, 1), *facts])
            step = {'BoolSplit': dict(condition=guard, **{'from': point_on(bound), 'to': source_on(bound)}, **cases)}
            left, right = point_on(rows), source_on(rows)
            point_laws.append(theorem([['rows', root_sort], ['query_key', key_sort]], left, right,
                {'Induction': dict(variable='rows', **{'from': left, 'to': right}, cases=[
                    dict(bindings=[], proof=convert(point_on(nil), source_on(nil))),
                    dict(bindings=['key', 'row', 'tail'], proof=step)])}))
        if indexed or dense_slots:
            from column_index import prepare as prepare_index
            original_sort=column_sort
            if dense_slots:
                from column_dense import prepare as prepare_dense
                index=prepare_dense(table,root_sort,column_sort,encode,decode,roundtrips[-1],point_functions[-1],point_laws[-1],operation_functions[-1],operation_laws[-1],function,theorem,datatype,objects,dense_slots)
            else:
                index=prepare_index(table,root_sort,cid,columns,selectors,encode,decode,roundtrips[-1],point_functions[-1],point_laws[-1],operation_functions[-1],operation_laws[-1],function,theorem,datatype,objects)
            physical[-1]=index['sort'];encodes[-1]=index['encode'];decodes[-1]=index['decode'];roundtrips[-1]=index['roundtrip']
            point_functions[-1]=index['point'];point_laws[-1]=index['point_law']
            operation_functions[-1]=index['operations'];operation_laws[-1]=index['operation_laws']
            for query_name,_,_,query in view_specs:
                old_read=ordered_functions[query_name];old_law=ordered_laws[query_name]
                result=objects[old_read]['payload']['declaration']['Function']['result']
                index_names=['index_base',*['index_aux_'+str(i)for i in range(dense_slots or 2)]]
                read=function([['indexed',index['sort']]],result,match(var('indexed'),[(index_names,call(old_read,[var('index_base')]))]))
                left=call(read,[call(index['encode'],[rows])]);middle=call(old_read,[call(encode,[rows])])
                ordered_functions[query_name]=read
                ordered_laws[query_name]=theorem([['view_rows',root_sort]],sub(left,{'rows':var('view_rows')}),query(var('view_rows')),
                    trans(convert(sub(left,{'rows':var('view_rows')}),sub(middle,{'rows':var('view_rows')})),use(old_law,[var('view_rows')])))
    return dict(fields=physical, encode=encodes, decode=decodes, roundtrips=roundtrips,
                points=point_functions, point_laws=point_laws,
                operations=operation_functions, operation_laws=operation_laws,
                ordered=ordered_functions, ordered_laws=ordered_laws)
