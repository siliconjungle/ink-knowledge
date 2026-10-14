import copy
import unittest
from producers.established_facts import specialize
from producers.semantic_laws import value, var, term, lam, op


class EstablishedFacts(unittest.TestCase):
    def fixture(self):
        boolean = value('Bool')
        predicate = var(boolean, 'arbitrary')
        equation = {'from':predicate,'to':term(boolean,{'Bool':True})}
        subject = dict(functions={},contexts={'observer':[dict(path=[],parameters={'arbitrary':boolean},conditions=[equation])]})
        core = dict(program=dict(functions=[],records={'Unrelated':[['field','U32']]},enums={}))
        return subject, core

    def test_arbitrary_equations_remain_explicit_premises(self):
        subject,core = self.fixture()
        rows = specialize(subject,core)
        self.assertEqual(len(rows),1)
        law = rows[0][1]
        self.assertEqual(law['conditions'],subject['contexts']['observer'][0]['conditions'])
        self.assertEqual(law['proof']['Trans']['right'],{'Hypothesis':0})
        self.assertEqual(law['definition_context']['records'],{})

    def test_unknown_parameters_and_open_binders_decline(self):
        subject,core = self.fixture()
        subject['contexts']['observer'][0]['parameters']={}
        self.assertEqual(specialize(subject,core),[])
        subject,core = self.fixture()
        subject['contexts']['observer'][0]['conditions'][0]['from']=term(value('Bool'),{'Bound':0})
        self.assertEqual(specialize(subject,core),[])

    def test_beta_reduction_does_not_capture_nested_binders(self):
        subject,core = self.fixture()
        boolean=value('Bool')
        original=op(boolean,'apply',lam(boolean,term(boolean,{'Bound':0})),var(boolean,'arbitrary'))
        subject['contexts']['observer'][0]['conditions'][0]['from']=original
        law=specialize(subject,core)[0][1]
        self.assertEqual(law['from'],var(boolean,'arbitrary'))
        self.assertEqual(law['proof']['Trans']['middle'],original)

    def test_duplicate_sites_and_unrelated_schemas_do_not_grow_closures(self):
        subject,core = self.fixture()
        original=specialize(subject,core)
        subject['contexts']['other']=copy.deepcopy(subject['contexts']['observer'])
        core['program']['records']['Another']=[['value','String']]
        self.assertEqual(specialize(subject,core)[0][1],original[0][1])
        self.assertEqual(len(specialize(subject,core)),1)


if __name__=='__main__':unittest.main()
