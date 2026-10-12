import bisect
import random
import tempfile
import unittest
from pathlib import Path
from ink_knowledge import Store,entry
from ink_knowledge.discovery_accelerator import LearnedIndex,Bloom,enable
from ink_knowledge.search_artifacts import publish,load

class ExactDiscovery(unittest.TestCase):
    def test_learned_index_matches_bisect_even_with_duplicates_and_corrupted_model(self):
        rng=random.Random(7)
        for keys in [[],[4],[4]*300,sorted(rng.randrange(10000) for _ in range(2000)),[i*i for i in range(1000)]]:
            index=LearnedIndex(keys,32)
            for q in [-1,0,4,100000,*[rng.randrange(10000) for _ in range(1000)]]:
                self.assertEqual(index.lower_bound(q),bisect.bisect_left(keys,q))
            if index.segments:
                start,end,lo,hi,error=index.segments[0];index.segments[0]=(start+100000,end,lo,hi,0)
                self.assertEqual(index.lower_bound(4),bisect.bisect_left(keys,4))
    def test_bloom_no_false_negatives(self):
        values=list(range(1000));b=Bloom(values)
        self.assertTrue(all(b.maybe(x) for x in values))
    def test_accelerated_discovery_matches_canonical_pages_and_old_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            objects=[entry('definition','test',{'name':str(i)},result={'Value':'U32' if i%2 else 'Bool'}) for i in range(50)]
            original=Store.publish(tmp,objects);pinned=Store(tmp,original.data/'snapshots'/(original.snapshot_id+'.json'))
            expected=pinned.query(kind='definition',result={'Value':'U32'},limit=7)
            enable(pinned,8);self.assertEqual(pinned.query(kind='definition',result={'Value':'U32'},limit=7),expected)
            self.assertEqual(pinned.query(operation='absent'),[])
            all_ids=sorted(original.members());self.assertEqual(pinned.query(after=all_ids[10],limit=7),all_ids[11:18])
            original.extend([entry('definition','test',{'name':'new'})]);self.assertEqual(pinned.query(limit=1024),all_ids)
            # Accelerator membership cannot authenticate changed object bytes.
            (pinned.data/'objects'/(all_ids[0]+'.json')).write_text('{}')
            with self.assertRaises(ValueError):pinned.object(all_ids[0])
    def test_search_artifacts_are_immutable_and_outside_proof_discovery(self):
        with tempfile.TemporaryDirectory() as tmp:
            store=Store.publish(tmp,[]);ob=publish(tmp,'observations',{'score':1.5})
            model=publish(tmp,'models',{'weight':.2},[ob]);self.assertEqual(load(tmp,'models',model),{'weight':.2})
            self.assertEqual(store.query(),[])
            path=Path(tmp)/'store/search-artifacts/observations'/(ob+'.json');path.write_text('{}')
            with self.assertRaises(ValueError):load(tmp,'models',model)


if __name__=='__main__':unittest.main()
