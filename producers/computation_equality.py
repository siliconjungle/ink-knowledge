"""Untrusted equality authoring around checked closed-traversal specializations.

Residual open folds use ordinary generalized induction. Lexical cases stay in
their own proof scopes; all proposed equations replay in the existing kernel.
"""
import json

from producers.action_replacement import call, cons, convert, var
from producers.equational import fresh_alpha
from producers.fold_chunks import compose
from producers.point_delta import free_variables, lift, normal, replace, sub, variables


class ComputationEquality:
    def __init__(self, chunks):
        self.chunks = chunks
        self.serial = 0
        self.fold_lemmas = {}
        self.active = set()

    def fresh(self, occupied, prefix):
        while True:
            name = prefix + str(self.serial)
            self.serial += 1
            if name not in occupied:
                return name

    def normalize(self, term, env, depth=0):
        self.chunks.tick()
        if depth > 64:
            raise ValueError('computation equality normalization depth')
        term = normal(term, self.chunks.objects,
                      opaque=self.chunks.helpers | self.chunks.closed | self.chunks.gates,
                      blocked=self.chunks.folds,heads=self.chunks.closed)
        # The small normalizer deliberately leaves unknown Match branches
        # untouched. Enter their syntax here, retaining every local binder.
        def visit(value, nesting):
            self.chunks.tick()
            if nesting > 64:
                raise ValueError('computation equality term depth')
            if not isinstance(value, dict):
                raise ValueError('computation equality needs a complete term')
            if 'Match' in value:
                node=value['Match']
                return {'Match':dict(scrutinee=visit(node['scrutinee'],nesting+1),
                    branches=[dict(bindings=b['bindings'],body=self.normalize(b['body'],
                        {**env,**{name:None for name in b['bindings']}},depth+1)) for b in node['branches']])}
            if 'Call' in value or 'Construct' in value:
                kind='Call' if 'Call' in value else 'Construct';node=value[kind]
                return {kind:dict(node,arguments=[visit(arg,nesting+1) for arg in node['arguments']])}
            if 'Binary' in value:
                node=value['Binary'];return {'Binary':dict(node,left=visit(node['left'],nesting+1),right=visit(node['right'],nesting+1))}
            if 'If' in value:
                node=value['If'];return {'If':{key:visit(child,nesting+1) for key,child in node.items()}}
            return value
        return fresh_alpha(visit(term, 0), {name: name for name in env})

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
            return self.chunks.objects[term['Call']['function']]['payload']['declaration']['Function']['result']
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
            equality = self.prove(changed,other_changed,env,0)
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
        # These local equations are unconditional. Check each in its own
        # universally quantified scope, then import it at the use site. This
        # keeps nested traversal/case congruences below the kernel depth limit
        # without borrowing any ambient action premise or raising that limit.
        proof = self.prove_local(a, z, env, 0, depth)
        names = sorted(free_variables(a) | free_variables(z))
        params = [[name, env[name]] for name in names]
        if any(ty is None for _, ty in params):
            raise ValueError('computation equality needs typed free variables')
        lemma = self.chunks.theorem(params, a, z, proof)
        return {'Use': dict(theorem=lemma, arguments=[var(name) for name in names], premises=[])}

    def prove_local(self, a, z, env, hypotheses=0, depth=0):
        self.chunks.tick()
        if depth > 24:
            raise ValueError('computation equality proof depth')
        left,right = self.normalize(a,env),self.normalize(z,env)
        def finish(proof):
            return compose([*([convert(a,left)] if a != left else []), proof,
                            *([convert(right,z)] if right != z else [])])
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
            if x['scrutinee'] != y['scrutinee']:
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
        for side, term in [('right', right), ('left', left)]:
            invocation = term.get('Call')
            if invocation and (invocation['function'] in self.chunks.helpers
                    or (self.chunks.objects[invocation['function']]['payload'].get('declaration',{}).get('Function',{}).get('recursive') is not None
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
                proof=compose([
                    lift({'Hypothesis':hypotheses},replace(left,scrutinee,var(hole)),hole),
                    self.prove(aa,zz,local,hypotheses+1,depth+1),
                    {'Sym':lift({'Hypothesis':hypotheses},replace(right,scrutinee,var(hole)),hole)},
                ])
                cases.append(dict(bindings=bindings,proof=proof))
            return finish({'Cases':dict(scrutinee=scrutinee,**{'from':left,'to':right},cases=cases)})
        # An ordinary checked conversion is also the fail-closed last attempt.
        # The authoring process never supplies its own success verdict.
        return finish(convert(left,right))
