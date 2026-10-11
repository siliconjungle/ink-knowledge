"""Untrusted dynamic-key point maintenance, with checked scalar and induction proofs.

Remove/replace repair the cached reply. Insert skips refresh for unrelated keys;
an insertion of the queried key evaluates the exact post-state query. There is
no sortedness premise, producer whitelist or trusted invalidation metadata.
"""
import json, os, subprocess, tempfile
from pathlib import Path
from producers.action_replacement import var, call, cons, convert, trans
from producers.cache_maintenance import leaves, variables
from producers.point_delta import legacy_setup as fixed_setup, binary, choice, match, sub, normal, equality, lift, replace

def setup(model, cache, add, objects):
    if 'Match' in cache['case']['normal']['Construct']['arguments'][0]:
        from producers.point_delta_mapped import setup as mapped_setup
        return mapped_setup(model,cache,add,objects,True)
    fixed = fixed_setup(model, cache, add, objects)
    table = fixed['table']
    if table.get('key_type','U64') != 'U64':
        raise ValueError('dynamic point tactic currently proves u64 keys')
    d, q, get, option, index = table['datatype'], fixed['q'], fixed['get'], fixed['option'], fixed['index']
    root_name = cache['case']['bindings'][index]
    rows, tail, head, value, target, new = map(var, ['dynamic_rows','dynamic_tail','dynamic_head','dynamic_value','dynamic_target','dynamic_new'])
    row_sort = objects[table['replace']]['payload']['declaration']['Function']['params'][2][1]
    getof = lambda r: call(get,[r,q])
    none = cons(option,0,[])
    some = fixed['some']
    nil, bound = cons(d,0,[]), cons(d,1,[head,value,tail])
    queried = binary('==',target,q)
    compiler = Path(os.environ.get('INK_COMPILER','target/debug/ink')).resolve()
    scalar_cache = {}
    def scalar(a,z,facts):
        key=json.dumps([a,z,facts],sort_keys=True)
        if key not in scalar_cache:
            from producers.bitvector_proofs import certificate
            names=sorted(variables([a,z,[list(x[:2]) for x in facts]]))
            goal=dict(params=[[n,'U64']for n in names],conditions=[dict(zip(['from','to'],x[:2]))for x in facts],**{'from':a,'to':z})
            with tempfile.TemporaryDirectory(prefix='ink-key-proof-') as directory:
                p=Path(directory);(p/'goal.json').write_text(json.dumps(goal))
                result=subprocess.run([str(compiler),'bitvector-obligation',str(p/'goal.json'),'-o',str(p/'cnf.json')],capture_output=True,text=True)
                if result.returncode:raise ValueError(result.stderr)
                scalar_cache[key]={'BitVector':dict(**{'from':a,'to':z},hypotheses=[x[2]for x in facts],certificate=certificate(json.loads((p/'cnf.json').read_text())))}
        return scalar_cache[key]
    laws={}
    for name in ['remove','replace','insert']:
        extra=[new]if name!='remove'else[]
        change=lambda r:call(table[name],[r,target]+extra)
        lhs=lambda r:getof(change(r))
        params=[['dynamic_rows',{'Data':d}],['dynamic_target','U64']]+([['dynamic_new',row_sort]]if extra else[])
        condition=dict(**{'from':queried,'to':{'Bool':False}})
        qtarget=binary('==',q,target)
        facts=[(queried,{'Bool':False},0),(qtarget,{'Bool':False},scalar(qtarget,{'Bool':False},[(queried,{'Bool':False},0)]))]
        guard=binary('<'if name=='insert'else'==',target,head)
        branches={}
        for flag in [False,True]:
            fs=[*facts,(guard,{'Bool':flag},2)]
            if flag and name!='insert':
                qhead=binary('==',q,head)
                fs.append((qhead,{'Bool':False},scalar(qhead,{'Bool':False},[(queried,{'Bool':False},0),(guard,{'Bool':True},2)])))
            branches['on_true'if flag else'on_false']=equality(lhs(bound),getof(bound),objects,(lhs(tail),getof(tail),1),fs)
        unaffected=add({'Theorem':dict(params=params,conditions=[condition],**{'from':lhs(rows),'to':getof(rows)},proof={'Induction':dict(variable='dynamic_rows',**{'from':lhs(rows),'to':getof(rows)},cases=[dict(bindings=[],proof=equality(lhs(nil),getof(nil),objects,facts=facts)),dict(bindings=['dynamic_head','dynamic_value','dynamic_tail'],proof={'BoolSplit':dict(condition=guard,**{'from':lhs(bound),'to':getof(bound)},**branches)})])})},[d,option])
        same = (none if name=='remove' else match(getof(rows),[([],none),(['dynamic_old'],some(new))])) if name!='insert' else lhs(rows)
        rhs=choice(queried,same,getof(rows))
        target_equal=scalar(target,q,[(queried,{'Bool':True},0)])
        if name=='insert':yes=convert(lhs(rows),lhs(rows))
        else:
            context=getof(call(table[name],[rows,var('delta_hole')]+extra))
            yes=trans(lift(target_equal,context),{'Use':dict(theorem=fixed['updates'][name],arguments=[rows]+extra,premises=[])})
        rhs_yes=lift({'Hypothesis':0},replace(rhs,queried,var('delta_hole')))
        rhs_no=lift({'Hypothesis':0},replace(rhs,queried,var('delta_hole')))
        proof={'BoolSplit':dict(condition=queried,**{'from':lhs(rows),'to':rhs},on_true=trans(yes,{'Sym':rhs_yes}),on_false=trans({'Use':dict(theorem=unaffected,arguments=[rows,target]+extra,premises=[{'Hypothesis':0}])},{'Sym':rhs_no}))}
        laws[name]=add({'Theorem':dict(params=params,conditions=[],**{'from':lhs(rows),'to':rhs},proof=proof)},[d,option])
    def recipe(t,old,bindings):
        if t==var(bindings[index]):return old
        x=t.get('Call',{});args=x.get('arguments',[])
        name=next((n for n in laws if table[n]==x.get('function')),None)
        if name is None or len(args)<2:raise ValueError('unsupported point update')
        prior=recipe(args[0],old,bindings)
        same=none if name=='remove'else match(prior,[([],none),(['dynamic_old'],some(args[2]))]) if name=='replace'else getof(t)
        return choice(binary('==',args[1],q),same,prior)
    def action(sa):
        def predict(t):
            if 'If'in t:
                x=t['If'];return choice(x['condition'],predict(x['on_true']),predict(x['on_false']))
            o=t['Construct']
            if o['constructor']!=0 or o['arguments'][1]!={'Bool':True}:return var('cached_reply')
            return recipe(o['arguments'][3]['Construct']['arguments'][index],var('cached_reply'),sa['case']['bindings'])
        try:return predict(sa['case']['normal'])
        except(ValueError,KeyError):return None
    def query_equality(t,bindings):
        if t==var(bindings[index]):return {'Refl':getof(t)}
        x=t['Call'];args=x['arguments'];name=next(n for n in laws if table[n]==x['function'])
        use={'Use':dict(theorem=laws[name],arguments=args,premises=[])}
        prior=getof(args[0]);same=none if name=='remove'else match(prior,[([],none),(['dynamic_old'],some(args[2]))]) if name=='replace'else getof(t)
        context=choice(binary('==',args[1],q),same,prior)
        return trans(use,lift(query_equality(args[0],bindings),replace(context,prior,var('delta_hole'))))
    return dict(action=action,recipe=recipe,equality=query_equality,index=index,get=get,q=q,option=option,table=table,some=some,laws=laws,
                start=lambda a,z,facts:equality(a,z,objects,facts=facts))
