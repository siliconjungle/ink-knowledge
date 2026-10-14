import unittest
from producers.physical_capabilities import persistent_records,paged_record_groups
class PersistentRecords(unittest.TestCase):
 def test_reachable_sequences_include_nested_words_and_exclude_temporary_helpers(self):
  named=lambda n:dict(Named=n)
  p=dict(records={'State':[('rows',dict(List=named('Row'))),('frontiers',dict(List=dict(List='U64')))],'Row':[('key','U32'),('value','U64'),('live','Bool')],'Temporary':[('key','U32')]},states=[dict(ty=dict(Table=['U32',named('State')]))])
  self.assertEqual(persistent_records(p),['@U64','Row'])
  self.assertEqual(list(paged_record_groups(persistent_records(p))),[('all',['@U64','Row']),('records',['Row'])])
  self.assertEqual(list(paged_record_groups(['Row'])),[('all',['Row'])])
  self.assertEqual(list(paged_record_groups(['@U64'],[False])),[])
  p['states']=[];self.assertEqual(persistent_records(p),[])
if __name__=='__main__':unittest.main()
