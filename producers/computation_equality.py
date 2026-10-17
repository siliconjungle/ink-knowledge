"""Untrusted equality authoring around checked closed-traversal specializations.

Residual open folds use ordinary generalized induction. Lexical cases stay in
their own proof scopes; all proposed equations replay in the existing kernel.
"""
import json

from producers.action_replacement import call, cons, convert, var
from producers.fold_chunks import compose
from producers.point_delta import binding_names, free_variables, lift, replace, sub, variables


class ComputationEquality:
    def __init__(self, chunks):
        self.chunks = chunks
        self.serial = 0
        self.fold_lemmas = {}
        self.active = set()
        self.equations = {}
        self.active_equations = set()
        self.conditions = []
        from producers.closed_equations import ClosedEquations
        self.closed_computation = ClosedEquations(chunks)

    def fresh(self, occupied, prefix):
        while True:
            name = prefix + str(self.serial)
            self.serial += 1
            if name not in occupied:
                return name

    def computation(self):
        if not hasattr(self, 'open_computation'):
            from producers.open_equations import OpenEquations
            self.open_computation = OpenEquations(self.chunks)
        return self.open_computation

    def normalize(self, term, env, depth=0):
        return self.computation().normalize(term, env, depth)[0]

    def sort(self, term, env):
        if 'Var' in term:
            return env[term['Var']]
        if 'U64' in term:
            return 'U64'
        if 'Bool' in term:
            return 'Bool'
        if 'Construct' in term:
            return {'Data': term['Construct']['datatype']}
        if 'Call' in term:
            declaration=self.chunks.objects[term['Call']['function']]['payload']['declaration']
            function=declaration.get('Function',declaration.get('AbstractFunction'))
            if function is None:raise ValueError('computation equality call type')
            return function['result']
        if 'If' in term:
            return self.sort(term['If']['on_true'], env)
        if 'Match' in term:
            node = term['Match']; datatype = self.sort(node['scrutinee'], env)['Data']
            fields = self.chunks.objects[datatype]['payload']['declaration']['Datatype']['constructors'][0]['fields']
            local = {**env, **{name: ({'Data': datatype} if ty == 'SelfType' else ty)
                     for name, ty in zip(node['branches'][0]['bindings'], fields)}}
            return self.sort(node['branches'][0]['body'], local)
        if 'Binary' in term:
            op = term['Binary']['op'].removeprefix('f32:')
            return 'Bool' if op in ('==','!=','<','<=','>','>=','&&','||','is_nan','is_finite') else 'U64'
        raise ValueError('unsupported computation equality sort')

    def reduce(self, term, env):
        value,first=self.computation().normalize(term,env);steps=[first]
        # A case premise can remain hidden behind a subsequently opened pure
        # wrapper. Reapply it to exposed syntax, writing every substitution.
        # These are proof assumptions in their actual scope, never norm-cache
        # facts or unconditional equations.
        for _ in range(16):
            changed=False
            for equation,index in self.conditions:
                left,first=self.computation().normalize(equation['from'],env)
                right,last=self.computation().normalize(equation['to'],env)
                if left==right:continue
                occupied=set(env)|variables([value,left,right])|binding_names([value,left,right])
                hole=self.fresh(occupied,'computation_fact_')
                context=replace(value,left,var(hole))
                if context==value:continue
                equality=compose([{'Sym':first},{'Hypothesis':index},last])
                steps.append(lift(equality,context,hole));value=replace(value,left,right)
                value,equality=self.computation().normalize(value,env);steps.append(equality);changed=True
            if not changed:return value,compose(steps)
        raise ValueError('computation equality conditional reduction budget')

    def fold_pair(self, left, right):
        first, second = left['function'], right['function']
        f, head, tail, update = self.chunks.folds[first]
        g, other_head, other_tail, other_update = self.chunks.folds[second]
        if f['params'][0][1] != g['params'][0][1] or f['result'] != g['result']:
            raise ValueError('open fold correspondence types')
        if left['arguments'][0] != right['arguments'][0]:
            raise ValueError('open fold correspondence rows')
        layout, actual = self.chunks.application_layout(first,left['arguments'][1:],g['params'][1:],right['arguments'][1:])
        params, values, other_values = layout
        key = json.dumps([first,second,layout],sort_keys=True,separators=(',',':'))
        if key in self.fold_lemmas:
            return self.fold_lemmas[key], [left['arguments'][0], *actual]
        if key in self.active or len(self.active) >= self.chunks.MAX_DEPTH:
            raise ValueError('open fold correspondence cycle/depth')
        self.active.add(key)
        try:
            names = {name for name,_ in params}
            rows_name = self.fresh(names,'equivalent_rows_'); names.add(rows_name)
            head_name = self.fresh(names,'equivalent_head_'); names.add(head_name)
            tail_name = self.fresh(names,'equivalent_tail_')
            rows, item, rest = var(rows_name), var(head_name), var(tail_name)
            datatype = f['params'][0][1]['Data']
            constructors = self.chunks.objects[datatype]['payload']['declaration']['Datatype']['constructors']
            if len(constructors)!=2 or constructors[0]['fields'] or len(constructors[1]['fields'])!=2:
                raise ValueError('open fold list shape')
            a,z = call(first,[rows,*values]),call(second,[rows,*other_values])
            nil = cons(datatype,0,[]); row = cons(datatype,1,[item,rest])
            base = convert(sub(a,{rows_name:nil}),sub(z,{rows_name:nil}))
            substitutions = {n:v for (n,_),v in zip(f['params'][1:],values)}
            substitutions.update({head:item,tail:rest})
            changed = sub(update,substitutions)
            substitutions = {n:v for (n,_),v in zip(g['params'][1:],other_values)}
            substitutions.update({other_head:item,other_tail:rest})
            other_changed = sub(other_update,substitutions)
            env = dict(params)
            env[head_name] = constructors[1]['fields'][0]
            env[tail_name] = {'Data':datatype}
            saved=self.conditions;self.conditions=[]
            try:equality = self.prove(changed,other_changed,env,0)
            finally:self.conditions=saved
            begin = call(first,[rest,*values[:-1],changed])
            end = call(second,[rest,*other_values[:-1],other_changed])
            step = compose([
                convert(sub(a,{rows_name:row}),begin),
                {'GeneralizedHypothesis':dict(index=0,arguments=[changed])},
                {'Call':dict(function=second,arguments=[{'Refl':rest},
                    *[{'Refl':v} for v in other_values[:-1]],equality])},
                convert(end,sub(z,{rows_name:row})),
            ])
            proof = {'GeneralizedInduction':dict(variable=rows_name,generalize=[params[-1][0]],
                **{'from':a,'to':z},cases=[dict(bindings=[],proof=base),
                    dict(bindings=[head_name,tail_name],proof=step)])}
            lemma = self.chunks.theorem([[rows_name,{'Data':datatype}],*params],a,z,proof)
            self.fold_lemmas[key] = lemma
            return lemma, [left['arguments'][0],*actual]
        finally:
            self.active.remove(key)

    def prove(self, a, z, env, hypotheses=0, depth=0):
        if a == z:
            return {'Refl': a}
        if depth % 4:
            return self.prove_local(a, z, env, hypotheses, depth)
        # Check each local equation in its own universally quantified scope,
        # retaining its explicit case premises at every use site. This
        # keeps nested traversal/case congruences below the kernel depth limit
        # without borrowing any ambient action premise or raising that limit.
        conditions=[equation for equation,_ in self.conditions]
        names = sorted(free_variables([a,z,conditions]))
        params = [[name, env[name]] for name in names]
        if any(ty is None for _, ty in params):
            raise ValueError('computation equality needs typed free variables')
        key = json.dumps([params,conditions,a,z], sort_keys=True, separators=(',', ':'))
        if key in self.active_equations:
            raise ValueError('computation equality equation cycle')
        lemma = self.equations.get(key)
        if lemma is None:
            self.active_equations.add(key)
            try:
                # This is a fresh universal theorem, with its own proof scope.
                # The global work bound and equation-cycle guard still span
                # every lemma; lexical proof depth starts at this new root.
                saved=self.conditions
                self.conditions=[(equation,index) for index,equation in enumerate(conditions)]
                try:proof = self.prove_local(a, z, env, len(conditions), 0)
                finally:self.conditions=saved
                lemma = self.chunks.theorem(params, a, z, proof,conditions=conditions)
                self.equations[key] = lemma
            finally:
                self.active_equations.remove(key)
        needed=self.chunks.objects[lemma]['payload']['declaration']['Theorem']['conditions']
        return {'Use': dict(theorem=lemma, arguments=[var(name) for name in names],
            premises=[{'Hypothesis':next(index for actual,index in self.conditions if actual==equation)} for equation in needed])}

    def prove_local(self, a, z, env, hypotheses=0, depth=0):
        self.chunks.tick()
        if depth > 24:
            raise ValueError('computation equality proof depth')
        # Compare matching context before opening its computations. In
        # particular a closed guard belongs in one unconditional equation,
        # rather than being re-evaluated inside every transition branch.
        if (not free_variables(a) and not free_variables(z)
                and ('U64' in z or 'Bool' in z)):
            value, equality = self.closed_computation.evaluate(a)
            if value != z:
                raise ValueError('closed computation endpoints differ')
            lemma = self.chunks.theorem([], a, z, equality)
            return {'Use': dict(theorem=lemma, arguments=[], premises=[])}
        if 'Call' in a and 'Call' in z and a['Call']['function'] == z['Call']['function']:
            x, y = a['Call'], z['Call']
            if len(x['arguments']) == len(y['arguments']):
                return {'Call': dict(function=x['function'], arguments=[
                    self.prove(v, w, env, hypotheses, depth+1)
                    for v, w in zip(x['arguments'], y['arguments'])])}
        if 'Binary' in a and 'Binary' in z and a['Binary']['op'] == z['Binary']['op']:
            x, y = a['Binary'], z['Binary']
            return {'Binary': dict(op=x['op'],
                left=self.prove(x['left'], y['left'], env, hypotheses, depth+1),
                right=self.prove(x['right'], y['right'], env, hypotheses, depth+1))}
        if 'If' in a and 'If' in z:
            x, y = a['If'], z['If']
            hole = self.fresh(set(env)|variables(a)|variables(z), 'computation_hole_')
            for first, second, reverse in [(a,z,False),(z,a,True)]:
                condition = first['If']['condition']
                if not free_variables(condition):
                    value, equality = self.closed_computation.evaluate(condition)
                    if 'Bool' not in value:
                        raise ValueError('closed conditional computation type')
                    chosen = first['If']['on_true' if value['Bool'] else 'on_false']
                    context = {'If':dict(first['If'], condition=var(hole))}
                    reduced = {'If':dict(first['If'], condition=value)}
                    proof = compose([lift(equality, context, hole), convert(reduced, chosen),
                                     self.prove(chosen,second,env,hypotheses,depth+1)])
                    return {'Sym':proof} if reverse else proof
            return compose([
                lift(self.prove(x['condition'], y['condition'], env, hypotheses, depth+1),
                     {'If':dict(condition=var(hole),on_true=x['on_true'],on_false=x['on_false'])}, hole),
                lift(self.prove(x['on_true'], y['on_true'], env, hypotheses, depth+1),
                     {'If':dict(condition=y['condition'],on_true=var(hole),on_false=x['on_false'])}, hole),
                lift(self.prove(x['on_false'], y['on_false'], env, hypotheses, depth+1),
                     {'If':dict(condition=y['condition'],on_true=y['on_true'],on_false=var(hole))}, hole),
            ])
        left,forward=self.reduce(a,env);right,backward=self.reduce(z,env)
        def finish(proof):
            return compose([forward,proof,{'Sym':backward}])
        if left == right:
            return finish(convert(left,right))
        if ('Call' in left and left['Call']['function'] in self.chunks.folds
                and not free_variables(left) and not free_variables(right)):
            return finish(self.chunks.closed_application(left['Call'],right))
        if 'Call' in left and 'Call' in right:
            x,y = left['Call'],right['Call']
            if x['function'] in self.chunks.folds and y['function'] in self.chunks.helpers:
                helper = self.chunks.objects[y['function']]['payload']['declaration']['Function']
                original = self.chunks.folds[x['function']][0]
                if (helper['params'] and helper['result'] == original['result']
                        and helper['params'][-1][1] == original['result']):
                    lemma,args = self.chunks.bridge_application(x,y)
                    return finish({'Use':dict(theorem=lemma,arguments=args,premises=[])})
            if x['function'] == y['function'] and len(x['arguments'])==len(y['arguments']):
                return finish({'Call':dict(function=x['function'],arguments=[self.prove(v,w,env,hypotheses,depth+1)
                    for v,w in zip(x['arguments'],y['arguments'])])})
            if x['function'] in self.chunks.folds and y['function'] in self.chunks.folds:
                lemma,args = self.fold_pair(x,y)
                return finish({'Use':dict(theorem=lemma,arguments=args,premises=[])})
        for first, second, reverse in [(left,right,False),(right,left,True)]:
            invocation=first.get('Call')
            if invocation and invocation['function'] in self.chunks.folds:
                rows=invocation['arguments'][0]
                if not free_variables(rows):
                    node=self.chunks.expose(rows)['Construct']
                    f,head,tail,step=self.chunks.folds[invocation['function']]
                    if node['constructor']==0 and not node['arguments']:
                        reduced=invocation['arguments'][-1]
                        opening=convert(first,reduced)
                    elif node['constructor']==1 and len(node['arguments'])==2:
                        item,rest=node['arguments']
                        bindings=dict(zip([n for n,_ in f['params'][1:]],invocation['arguments'][1:]))
                        bindings.update({head:item,tail:rest})
                        reduced=call(invocation['function'],[rest,*invocation['arguments'][1:-1],sub(step,bindings)])
                        lemma=self.chunks.cons_equation(invocation['function'])
                        opening=compose([convert(first,call(invocation['function'],[
                            cons(node['datatype'],1,[item,rest]),*invocation['arguments'][1:]])),
                            {'Use':dict(theorem=lemma,arguments=[item,rest,*invocation['arguments'][1:]],premises=[])}])
                    else:
                        raise ValueError('closed fold correspondence list shape')
                    proof=compose([opening,self.prove(reduced,second,env,hypotheses,depth+1)])
                    return finish({'Sym':proof} if reverse else proof)
        if 'Construct' in left and 'Construct' in right:
            x,y = left['Construct'],right['Construct']
            if (x['datatype'],x['constructor']) == (y['datatype'],y['constructor']):
                return finish({'Construct':dict(datatype=x['datatype'],constructor=x['constructor'],
                    arguments=[self.prove(v,w,env,hypotheses,depth+1) for v,w in zip(x['arguments'],y['arguments'])])})
        if 'Binary' in left and 'Binary' in right and left['Binary']['op']==right['Binary']['op']:
            x,y=left['Binary'],right['Binary']
            return finish({'Binary':dict(op=x['op'],left=self.prove(x['left'],y['left'],env,hypotheses,depth+1),
                right=self.prove(x['right'],y['right'],env,hypotheses,depth+1))})
        if 'If' in left and 'If' in right:
            x,y=left['If'],right['If'];hole=self.fresh(set(env)|variables(left)|variables(right),'computation_hole_')
            condition=self.prove(x['condition'],y['condition'],env,hypotheses,depth+1)
            yes=self.prove(x['on_true'],y['on_true'],env,hypotheses,depth+1)
            no=self.prove(x['on_false'],y['on_false'],env,hypotheses,depth+1)
            return finish(compose([
                lift(condition,{'If':dict(condition=var(hole),on_true=x['on_true'],on_false=x['on_false'])},hole),
                lift(yes,{'If':dict(condition=y['condition'],on_true=var(hole),on_false=x['on_false'])},hole),
                lift(no,{'If':dict(condition=y['condition'],on_true=y['on_true'],on_false=var(hole))},hole),
            ]))
        if 'Match' in left and 'Match' in right:
            x,y=left['Match'],right['Match']
            if (x['scrutinee'] != y['scrutinee']
                    and self.sort(x['scrutinee'],env) == self.sort(y['scrutinee'],env)):
                # Equal sums must share one case split. Splitting each side
                # independently would introduce unrelated payload variables.
                hole=self.fresh(set(env)|variables(left)|variables(right),'computation_hole_')
                equality=self.prove(x['scrutinee'],y['scrutinee'],env,hypotheses,depth+1)
                context={'Match':dict(scrutinee=var(hole),branches=x['branches'])}
                middle={'Match':dict(scrutinee=y['scrutinee'],branches=x['branches'])}
                return finish(compose([lift(equality,context,hole),
                    self.prove(middle,right,env,hypotheses,depth+1)]))
        # Pure wrappers may return a projection/freeze of an owned accumulator,
        # rather than that accumulator itself. Expose one checked definition
        # before splitting its result into unrelated constructor fields. Keep
        # its chunk callees opaque so their universal fold bridges remain small.
        # Open source wrappers before generated chunks. The wrapper may expose
        # the original fold, allowing its universal bridge to retain the whole
        # balanced helper graph. Opening every selected helper first instead
        # expands the computation into one large conversion with copied live
        # captures. This is only proposal order; every equation still checks.
        sides = [('right', right), ('left', left)]
        sides.sort(key=lambda item: item[1].get('Call', {}).get('function') in self.chunks.helpers)
        for side, term in sides:
            invocation = term.get('Call')
            definition = (self.chunks.objects[invocation['function']]['payload'].get('declaration',{}).get('Function')
                          if invocation else None)
            if definition and (invocation['function'] in self.chunks.helpers
                    or definition['recursive'] is None
                    or (definition['recursive'] is not None
                        and self.chunks.acyclic(invocation['function']))):
                helper = self.chunks.objects[invocation['function']]['payload']['declaration']['Function']
                body = sub(helper['body'], dict(zip([n for n, _ in helper['params']], invocation['arguments'])))
                opened = self.chunks.unfold(invocation['function'],invocation['arguments'])
                if side == 'right':
                    return finish(compose([self.prove(left,body,env,hypotheses,depth+1), {'Sym':opened}]))
                return finish(compose([opened, self.prove(body,right,env,hypotheses,depth+1)]))
        node = left.get('Match',right.get('Match'))
        if node:
            scrutinee=node['scrutinee'];sort=self.sort(scrutinee,env)
            if not isinstance(sort,dict) or 'Data' not in sort:
                raise ValueError('computation equality case type')
            invocation=scrutinee.get('Call')
            if invocation and invocation['function'] in self.chunks.gates:
                function=self.chunks.objects[invocation['function']]['payload']['declaration']['Function']
                body=sub(function['body'],dict(zip([n for n,_ in function['params']],invocation['arguments'])))
                equality=self.chunks.unfold(invocation['function'],invocation['arguments'])
                occupied=set(env)|variables([left,right,body])|binding_names([left,right,body])
                hole=self.fresh(occupied,'computation_gate_result_')
                def transport(term):
                    context=replace(term,scrutinee,var(hole))
                    return {'Refl':term} if context==term else lift(equality,context,hole)
                return finish(compose([transport(left),
                    self.prove(replace(left,scrutinee,body),replace(right,scrutinee,body),env,hypotheses,depth+1),
                    {'Sym':transport(right)}]))
            if not free_variables(scrutinee):
                value,equality=self.closed_computation.evaluate(scrutinee)
                exposed=self.chunks.expose(value)
                equality=compose([equality,convert(value,exposed)])
                occupied=set(env)|variables([left,right,exposed])|binding_names([left,right,exposed])
                hole=self.fresh(occupied,'computation_closed_case_')
                def transport(term):
                    context=replace(term,scrutinee,var(hole))
                    return {'Refl':term} if context==term else lift(equality,context,hole)
                return finish(compose([transport(left),
                    self.prove(replace(left,scrutinee,exposed),replace(right,scrutinee,exposed),env,hypotheses,depth+1),
                    {'Sym':transport(right)}]))
            datatype=sort['Data'];cases=[]
            for index,constructor in enumerate(self.chunks.objects[datatype]['payload']['declaration']['Datatype']['constructors']):
                occupied=set(env)|variables(left)|variables(right);bindings=[]
                for _ in constructor['fields']:
                    name=self.fresh(occupied,'computation_case_');occupied.add(name);bindings.append(name)
                value=cons(datatype,index,[var(name) for name in bindings])
                local={**env,**{name:({'Data':datatype} if ty=='SelfType' else ty)
                    for name,ty in zip(bindings,constructor['fields'])}}
                aa,zz=replace(left,scrutinee,value),replace(right,scrutinee,value)
                hole=self.fresh(set(local)|variables(left)|variables(right),'computation_hole_')
                self.conditions.append((dict(**{'from':scrutinee,'to':value}),hypotheses))
                try:middle=self.prove(aa,zz,local,hypotheses+1,depth+1)
                finally:self.conditions.pop()
                proof=compose([
                    lift({'Hypothesis':hypotheses},replace(left,scrutinee,var(hole)),hole),
                    middle,
                    {'Sym':lift({'Hypothesis':hypotheses},replace(right,scrutinee,var(hole)),hole)},
                ])
                cases.append(dict(bindings=bindings,proof=proof))
            return finish({'Cases':dict(scrutinee=scrutinee,**{'from':left,'to':right},cases=cases)})
        # An ordinary checked conversion is also the fail-closed last attempt.
        # The authoring process never supplies its own success verdict.
        return finish(convert(left,right))
