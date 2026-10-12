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
