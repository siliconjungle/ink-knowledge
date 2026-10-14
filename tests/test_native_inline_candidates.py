import unittest
from producers.native_inline import choices,propose

class NativeInlining(unittest.TestCase):
 def test_frequency_guidance_bounds_and_source_names(self):
  records={'Carrier':[['items',{'List':'U32'}],['other',{'List':'U32'}],['stamp','U32']]}
  functions=[dict(name=n,params=[['x',{'Named':'Carrier'}]],result='U32',body={'Field':[{'Var':'x'},'stamp']})for n in ['hot','cold','unobserved']]
  core={'program':{'records':records,'functions':functions}}
  rows=list(choices(core,{'call:hot':100,'call:cold':1},counts=[1,2,4]));self.assertEqual(rows,[['hot'],['cold','hot']])
  self.assertEqual(list(choices(core,{},counts=[1])),[])
  with self.assertRaises(ValueError):list(choices(core,{},counts=[4097]))
  physical={'schema':1,'input_core_sha256':'source','buffers':'direct','borrow_reads':['existing']}
  context=dict(core=core,source='source',physical=physical,frequencies={'call:hot':100},emit_target='rust')
  row=list(propose(context,counts=[1]))[0];self.assertEqual(row['step']['package']['borrow_reads'],['existing']);self.assertNotIn('inline_functions',physical)
  self.assertEqual(list(propose(dict(context,emit_target='javascript'),counts=[1])),[])
  self.assertEqual(list(propose(dict(context,representation={'selected':'other'}),counts=[1])),[])

if __name__=='__main__':unittest.main()
