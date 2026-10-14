"""Conditional induction authoring must retain every premise and lexical scope."""
import unittest
from producers.conditional_induction import guarded_goal, apply_guarded, fresh_hole, TRUE, FALSE


class ConditionalInduction(unittest.TestCase):
    def test_guards_preserve_declaration_order_and_all_premises(self):
        first={'Var':'first'};second={'Var':'second'}
        goal=dict(params=[['first','Bool'],['second','Bool']],
            conditions=[dict(**{'from':first,'to':TRUE}),dict(**{'from':second,'to':TRUE})],
            goal=dict(**{'from':FALSE,'to':TRUE}))
        guard,proof,statement=guarded_goal(goal)
        self.assertEqual(guard['If']['condition'],first)
        self.assertEqual(guard['If']['on_true']['If']['condition'],second)
        self.assertEqual(statement['If']['on_true'],FALSE)
        self.assertEqual(statement['If']['on_false'],TRUE)
        def hypotheses(term):
            if isinstance(term,dict):
                return ({term['Hypothesis']} if 'Hypothesis'in term else set()).union(*(hypotheses(v)for v in term.values()))
            if isinstance(term,list):return set().union(*(hypotheses(v)for v in term))
            return set()
        self.assertEqual(hypotheses(proof),{0,1})

    def test_substitution_hole_cannot_capture_an_existing_parameter(self):
        value={'Var':'conditional_hole'}
        goal=dict(params=[['conditional_hole','Bool'],['conditional_hole_','Bool']],
            conditions=[dict(**{'from':value,'to':TRUE})],goal=dict(**{'from':value,'to':TRUE}))
        guard,proof,_=guarded_goal(goal)
        self.assertEqual(fresh_hole(goal),'conditional_hole__')
        use=apply_guarded(goal,guard,proof,'a'*64)
        self.assertIn('conditional_hole__',str(use))
        self.assertEqual(use['Trans'][0]['Trans'][0]['Convert']['from'],value)

    def test_unavailable_guard_translation_does_not_invent_a_premise(self):
        goal=dict(params=[],conditions=[dict(**{'from':TRUE,'to':FALSE})],goal=dict(**{'from':TRUE,'to':FALSE}))
        self.assertIsNone(guarded_goal(goal))


if __name__=='__main__':unittest.main()
