"""Bounded proof authoring regressions; kernel replay lives in distribution tests."""
import sys,unittest
from pathlib import Path
sys.path[:0]=[str(Path(__file__).resolve().parents[1]),str(Path(__file__).resolve().parents[1]/'producers')]
from producers.point_delta import sub
from producers.state_calculus import CanonicalLibrary,build

class ComposableState(unittest.TestCase):
    def test_substitution_preserves_caller_tail_under_same_named_match(self):
        term={'Match':dict(scrutinee={'Var':'xs'},branches=[dict(bindings=[],body={'Var':'xs'}),dict(bindings=['head','tail'],body={'Var':'xs'})])}
        caller={'Construct':dict(datatype='list',constructor=1,arguments=[{'Var':'head'},{'Var':'tail'}])}
        replaced=sub(term,{'xs':caller})
        self.assertEqual(replaced['Match']['scrutinee'],caller)
        self.assertEqual(replaced['Match']['branches'][1]['body'],caller)
        self.assertNotIn('head',replaced['Match']['branches'][1]['bindings'])
        self.assertNotIn('tail',replaced['Match']['branches'][1]['bindings'])
    def test_checked_candidates_are_reproducible_and_not_special_cases(self):
        a,b=build(CanonicalLibrary()),build(CanonicalLibrary())
        self.assertEqual(a.objects,b.objects)
        self.assertEqual(a.names,b.names)
        for name in ('repair_composition','roundtrip_composition','step_correspondence_composition','shared_fold_exact','lookup_replace_other_key','bounded_insertion_fold_exact','shared_left_fold_exact','group_remove_repair_exact','group_replace_repair_exact','join_indexed_exact','partition_encoded_lookup','lookup_general_replace'):
            self.assertIn(name,a.names)
        # Shared ordered folds need no algebraic assumptions.
        declaration=a.objects[a.names['shared_fold_exact']]['payload']['declaration']['Theorem']
        self.assertEqual(declaration['conditions'],[])

if __name__=='__main__':unittest.main()
