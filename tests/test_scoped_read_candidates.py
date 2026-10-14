import unittest
from ink_knowledge import identity
from producers.planning_recipes import lexical_reads
from producers.readonly_borrows import scoped_candidates

class ScopedReadCandidates(unittest.TestCase):
 def test_same_named_scalar_is_not_promoted_from_another_functions_list(self):
  program=dict(records={'Item':[['value','U32']]},enums={},states=[],functions=[
   dict(name='scalar',params=[['x','U32']],result='U32',body={'Var':'x'}),
   dict(name='retained',params=[['x',{'List':{'Named':'Item'}}]],result={'List':{'Named':'Item'}},body={'Var':'x'}),
   dict(name='field',params=[['x',{'Named':'Item'}]],result='U32',body={'Field':[{'Var':'x'},'value']}),
  ])
  self.assertIn(identity({'Var':'x'}),lexical_reads(program))
  self.assertNotIn(identity({'Var':'x'}),lexical_reads(program,only_function='scalar'))
  def site(function):return identity({'capability':'ink-function-read-v1','function':function,'expression':identity({'Var':'x'})})
  rows=list(scoped_candidates(dict(core={'program':program},source='a'*64,emit_target='rust')))
  observations=[r['step']['package']['borrow_reads']for r in rows if 'observations/'in r['label']]
  self.assertTrue(observations)
  self.assertTrue(all(site('scalar')not in sites for sites in observations))
  self.assertTrue(any(site('retained')in sites for sites in observations))

if __name__=='__main__':unittest.main()
