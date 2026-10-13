import tempfile,unittest
from pathlib import Path
from ink_knowledge import Store
from producers.value_boundary_measurements import publish,select
class BoundaryEvidence(unittest.TestCase):
 def test_comparable_phases_select_and_missing_shapes_retain_baseline(self):
  with tempfile.TemporaryDirectory()as tmp:
   target=dict(hardware='test',driver='test',toolchain='test',backend='cpu',bridge='test')
   report=dict(schema=1,instrumented=False,fixture='List<u32>',measurements=[dict(candidate=label,rows=32,reads=4,phase='lifecycle',samples_ns=[str(cost)]*9,input_bytes=300)for label,cost in [('materialized',100),('borrowed',60),('indexed',70),('packed',80)]])
   manifest=publish(Path(tmp),report,target,'a'*64,'b'*64);store=Store(tmp);store.rebuild()
   self.assertEqual(select(store,manifest)[0]['selected'],'borrowed')
   manifest['groups'][0]['workload']['shape']['rows']=33
   self.assertEqual(select(store,manifest)[0]['selected'],'materialized')
   report['instrumented']=True
   with self.assertRaises(ValueError):publish(Path(tmp),report,target,'a'*64,'b'*64)
if __name__=='__main__':unittest.main()
