"""Independent finite oracles for excluded points and relational narrowing."""
import random
import unittest
from producers.semantic_laws import value, var, word, op, term
from producers.word_facts import Facts, analyse, candidates, refine, _FactMemo
from tests.test_word_facts import evaluate


class ConditionalWordFacts(unittest.TestCase):
    def expressions(self, kind):
        sort = value(kind)
        return sort, var(sort, 'x'), var(sort, 'y')

    def boolean(self, b):
        return term(value('Bool'), {'Bool': b})

    def test_excluded_points_cross_wrapping_bijections_and_stay_branch_local(self):
        boolean = value('Bool')
        for kind, width in [('U32', 32), ('U64', 64)]:
            sort, x, _ = self.expressions(kind)
            mask = (1 << width) - 1
            for excluded in [0, 1, 4, mask-1, mask]:
                guard = op(boolean, 'binary:!=', x, word(kind, excluded))
                for name, function in [('binary:+', lambda a,b:a+b),
                                       ('binary:-', lambda a,b:a-b),
                                       ('call:word_xor', lambda a,b:a^b)]:
                    for k in [0, 3, mask]:
                        for reverse in [False, True]:
                            operands = [x, word(kind,k)]
                            numbers = [excluded,k]
                            if reverse:operands.reverse();numbers.reverse()
                            result = op(sort,name,*operands)
                            forbidden = word(kind,function(*numbers)&mask)
                            decision = op(boolean,'binary:!=',result,forbidden)
                            source = op(boolean,'call:choose',guard,decision,self.boolean(True))
                            self.assertEqual(analyse(source).constant, 1)
                            for n in [0,1,4,mask,mask-1,excluded]:
                                self.assertEqual(evaluate(source,dict(x=n)),1)
                            # Removing the guard is invalid at x == excluded.
                            self.assertIsNone(analyse(decision).constant)

    def test_relational_narrowing_composes_without_inverting_wrapping_arithmetic(self):
        boolean = value('Bool')
        for kind, width in [('U32',32),('U64',64)]:
            sort,x,y = self.expressions(kind)
            upper = op(boolean,'binary:<=',y,word(kind,256))
            for left in [x,op(sort,'binary:+',x,word(kind,1))]:
                guard = op(boolean,'binary:&&',op(boolean,'binary:<',left,y),upper)
                masked = op(sort,'call:word_and',left,word(kind,255))
                source = op(sort,'call:choose',guard,masked,left)
                self.assertIn(('branch-scoped-facts',left),list(candidates(source)))
                # A bound on the wrapped sum is not a bound on its input.
                if left != x:
                    wrong = op(sort,'call:choose',guard,
                               op(sort,'call:word_and',x,word(kind,255)),x)
                    self.assertNotIn(('branch-scoped-facts',x),list(candidates(wrong)))
            # False disjunction supplies the same pair of facts.
            guard = op(boolean,'binary:||',op(boolean,'binary:>=',x,y),
                       op(boolean,'binary:>',y,word(kind,256)))
            source = op(sort,'call:choose',guard,x,op(sort,'call:word_and',x,word(kind,255)))
            self.assertIn(('branch-scoped-facts',x),list(candidates(source)))

    def test_noninjective_operations_and_branch_joins_do_not_invent_exclusions(self):
        boolean=value('Bool')
        for kind,width in [('U32',32),('U64',64)]:
            sort,x,_=self.expressions(kind)
            scope=refine([],op(boolean,'binary:!=',x,word(kind,4)),True)
            product=op(sort,'binary:*',x,word(kind,2))
            self.assertIsNone(analyse(product,_scope=scope).excludes)
            self.assertEqual(evaluate(product,dict(x=4+(1<<(width-1)))),8)
            flag=var(boolean,'flag')
            for alternative,expected in [(0,4),(4,None)]:
                joined=op(sort,'call:choose',flag,x,word(kind,alternative))
                self.assertEqual(analyse(joined,_scope=scope).excludes,expected)
            with self.assertRaises(ValueError):Facts(width,minimum=4,maximum=4,excludes=4)

    def test_generated_branch_facts_agree_with_independent_values_and_cached_queries(self):
        rng=random.Random(624801)
        boolean=value('Bool')
        for kind,width in [('U32',32),('U64',64)]:
            sort,x,y=self.expressions(kind);mask=(1<<width)-1
            inputs=list(range(17))+[255,256,mask-1,mask]+[rng.getrandbits(width) for _ in range(12)]
            for _ in range(55):
                subject=rng.choice([x,y,op(sort,'binary:+',x,word(kind,1))])
                guard=op(boolean,'binary:'+rng.choice(['<','<=','>','>=','==','!=']),
                         subject,rng.choice([x,y,word(kind,rng.choice([0,4,16,256,mask]))]))
                tail=op(boolean,'binary:'+rng.choice(['!=','<=']),y,word(kind,16))
                guard=op(boolean,rng.choice(['binary:&&','binary:||']),guard,tail)
                payload=op(sort,rng.choice(['binary:+','binary:-','call:word_xor','binary:*']),subject,word(kind,3))
                source=op(sort,'call:choose',guard,payload,subject)
                facts=analyse(source);memo=_FactMemo()
                self.assertEqual(facts,analyse(source,_memo=memo))
                alternatives=list(candidates(source))
                for a in inputs:
                    for b in inputs:
                        actual=evaluate(source,dict(x=a,y=b))
                        self.assertLessEqual(facts.minimum,actual)
                        self.assertGreaterEqual(facts.maximum,actual)
                        self.assertEqual(actual&facts.zero,0)
                        self.assertEqual(actual&facts.one,facts.one)
                        self.assertNotEqual(actual,facts.excludes)
                        for _,replacement in alternatives:
                            self.assertEqual(actual,evaluate(replacement,dict(x=a,y=b)))

    def test_excluded_facts_do_not_cross_cached_scopes_or_analysis_modes(self):
        boolean=value('Bool');sort,x,y=self.expressions('U32')
        expression=op(sort,'binary:+',x,word('U32',3));memo=_FactMemo()
        for excluded in [4,7,0,None,4]:
            scope=[] if excluded is None else [(x,Facts(32,excludes=excluded))]
            for relational in [True,False]:
                self.assertEqual(analyse(expression,_scope=scope,_relational=relational),
                    analyse(expression,_scope=scope,_relational=relational,_memo=memo))
        # A plain signed/float carrier must not inherit unsigned reasoning.
        for kind in ['I32','F32']:
            with self.assertRaises(ValueError):analyse(var(value(kind),'x'))


if __name__=='__main__':unittest.main()
