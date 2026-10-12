import copy,random,unittest
from ink_knowledge.template_matching import TemplateSites
from ink_knowledge.law_templates import infer
from ink_planner.semantic_search import positions
from producers.semantic_laws import value,var,op,lam,bound

class TemplateMatching(unittest.TestCase):
    def test_index_matches_exhaustive_inference_with_holes_and_overloads(self):
        random.seed(17)
        a=value({'Named':'$A'});u=value('U32');s=value('String')
        def tree(depth):
            sort=random.choice([u,s])
            if not depth:return var(sort,'x')
            return op(sort,random.choice(['call:f','call:g','method:map']),tree(depth-1),tree(depth-1))
        subject={'functions':{str(i):tree(4)for i in range(8)}}
        patterns=[var(a,'hole'),op(a,'call:f',var(a,'hole'),var(a,'other')),lam(a,bound(a,0)),var(u,'literal')]
        index=TemplateSites(subject)
        for pattern in patterns:
            params={'hole':a,'other':a};types=['A']if '$A'in str(pattern)else []
            expected=[]
            for name,root in subject['functions'].items():
                for path,actual in positions(root):
                    bindings={}
                    if infer(pattern,actual,params,types,bindings)and set(bindings)==set(types):expected.append((name,path,actual,bindings))
            self.assertEqual(list(index.matches(pattern,params,types)),expected)
    def test_irrelevant_heads_do_not_consume_inference_budget(self):
        u=value('U32');x=var(u,'x');subject={'functions':{'f':op(u,'call:root',*[op(u,'call:other',x)for _ in range(1000)])}}
        index=TemplateSites(subject,attempt_limit=1)
        for i in range(1024):self.assertEqual(list(index.matches(op(u,'call:absent'+str(i),x),{'x':u},[])),[])
        self.assertEqual(index.attempts,0)
        self.assertEqual(len(list(index.matches(op(u,'call:root',var(u,'xs')),{'xs':u},[]))),0)
        self.assertEqual(index.attempts,1)
        with self.assertRaisesRegex(ValueError,'inference budget'):list(index.matches(x,{'x':u},[]))
        with self.assertRaisesRegex(ValueError,'subject node budget'):TemplateSites(subject,node_limit=20)

    def test_literals_sorts_and_nested_operations_skip_same_head_misses(self):
        u=value('U32');seq=value({'List':'U32'});x=var(u,'x')
        subject={'functions':{str(i):op(u,'call:f',dict(sort=u,node={'Word':i}))for i in range(512)}}
        index=TemplateSites(subject,attempt_limit=1)
        pattern=op(u,'call:f',dict(sort=u,node={'Word':17}))
        self.assertEqual(len(list(index.matches(pattern,{},[]))),1)
        self.assertEqual(index.attempts,1)
        # Composite constructors contain holes; treating them as literal leaves
        # would incorrectly discard valid matches.
        cons=dict(sort=seq,node={'Cons':[x,dict(sort=seq,node='Nil')]})
        actual=dict(sort=seq,node={'Cons':[dict(sort=u,node={'Word':7}),dict(sort=seq,node='Nil')]})
        self.assertEqual(len(list(TemplateSites({'functions':{str(i):actual for i in range(32)}}).matches(cons,{'x':u},[]))),32)
        with self.assertRaisesRegex(ValueError,'structural token budget'):
            list(TemplateSites(subject,token_limit=1).matches(pattern,{},[]))

    def test_applied_holes_preserve_arbitrary_bodies_and_binding_order(self):
        from producers.semantic_laws import arrow
        a=value({'Named':'$A'});u=value('U32');f=var(arrow(a,a),'f')
        pattern=lam(a,op(a,'apply',f,bound(a,0)))
        actual=lam(u,op(u,'binary:+',bound(u,0),dict(sort=u,node={'Word':1})))
        subject={'functions':{str(i):actual for i in range(64)}};sites=TemplateSites(subject)
        expected=[]
        for name,root in subject['functions'].items():
            for path,target in positions(root):
                bindings={}
                if infer(pattern,target,{'f':f['sort']},['A'],bindings):expected.append((name,path,target,bindings))
        self.assertEqual(list(sites.matches(pattern,{'f':f['sort']},['A'])),expected)
