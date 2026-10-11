#!/usr/bin/env python3
"""Independent finite checks of proposed tree algorithms; never proof authority."""
import random
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from producers.sequence_tree_fixture import generate
import tempfile
import json


def run():
    with tempfile.TemporaryDirectory(prefix='ink-sequence-tree-') as directory:
        names = generate(Path(directory))
        objects = json.loads((Path(directory)/'view.json').read_text())['objects']
        functions = {i:o['payload']['declaration']['Function'] for i,o in objects.items() if 'Function' in o['payload']['declaration']}
        work = [0]
        def evaluate(term, env, current=None):
            work[0] += 1
            if work[0] > 10_000_000:
                raise ValueError('finite checker work bound')
            kind, x = next(iter(term.items()))
            if kind == 'Var': return env[x]
            if kind in ('Bool','U64'): return x
            if kind == 'Construct': return (x['constructor'],tuple(evaluate(t,env,current) for t in x['arguments']))
            if kind == 'Call': return invoke(x['function'],[evaluate(t,env,current) for t in x['arguments']])
            if kind == 'SelfCall': return invoke(current,[evaluate(t,env,current) for t in x])
            if kind == 'If': return evaluate(x['on_true'] if evaluate(x['condition'],env,current) else x['on_false'],env,current)
            if kind == 'Match':
                tag, fields = evaluate(x['scrutinee'],env,current)
                branch=x['branches'][tag]
                return evaluate(branch['body'],dict(env,**dict(zip(branch['bindings'],fields))),current)
            if kind == 'Binary':
                a,b=evaluate(x['left'],env,current),evaluate(x['right'],env,current)
                return {'+':lambda:(a+b)%(2**64),'<':lambda:a<b,'>':lambda:a>b,'>=':lambda:a>=b,'==':lambda:a==b,'||':lambda:a or b}[x['op']]()
            raise ValueError(kind)
        def invoke(i,args):
            f=functions[i]
            return evaluate(f['body'],dict(zip([p[0] for p in f['params']],args)),i)
        def rows(xs):
            result=(0,())
            for k,v in reversed(xs): result=(1,(k,v,result))
            return result
        def decode(tree):
            result=invoke(names['decode'],[tree]);xs=[]
            while result[0]:
                k,v,result=result[1];xs.append((k,v))
            return xs
        def check_shape(t):
            if t[0]==0:return (2**64-1,0,0,0)
            if t[0]==1:return (t[1][0],t[1][0],1,1)
            l,r,lo,hi,h,n=t[1];a,b=check_shape(l),check_shape(r)
            assert l[0] and r[0]
            assert abs(a[2]-b[2])<=1,(a[2],b[2])
            assert (lo,hi,h,n)==(min(a[0],b[0]),max(a[1],b[1]),max(a[2],b[2])+1,a[3]+b[3])
            return lo,hi,h,n
        rng=random.Random(718431)
        for ordered in [False,True]:
            expected=[(rng.randrange(16),rng.randrange(2**64)) for _ in range(40)]
            if ordered:expected.sort(key=lambda x:x[0])
            tree=invoke(names['encode'],[rows(expected)])
            for step in range(250):
                work[0]=0
                assert decode(tree)==expected
                check_shape(tree)
                key=rng.choice([0,2**64-1,rng.randrange(20)])
                assert invoke(names['get'],[tree,key])==next(((1,(v,)) for k,v in expected if k==key),(0,()))
                before=tree
                op=rng.choice(['insert','replace','remove'])
                value=rng.randrange(2**64)
                tree=invoke(names[op],[tree,key]+([value] if op!='remove' else []))
                if op=='insert':
                    position=next((i for i,(k,_) in enumerate(expected) if key<k),len(expected))
                    expected.insert(position,(key,value))
                elif op=='replace':expected=[(k,value if k==key else v) for k,v in expected]
                else:expected=[x for x in expected if x[0]!=key]
                assert decode(before)!=expected or op=='replace' or op=='remove'
            assert decode(tree)==expected
        print('500 mixed ordered/unordered histories: exact order, duplicates, bounds, AVL balance and retained roots passed')


if __name__=='__main__':
    sys.setrecursionlimit(10000)
    run()
