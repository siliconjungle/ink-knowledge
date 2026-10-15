"""Invocation-local normalization reuse preserves scopes, modes and work limits."""
import copy
import unittest
from unittest.mock import patch
from producers import point_delta as p


def chain(depth):
    objects={}
    for i in range(depth+1):
        body=p.var('x')if i==0 else p.binary('+',p.call(str(i-1),[p.var('x')]),p.call(str(i-1),[p.var('x')]))
        objects[str(i)]={'payload':{'declaration':{'Function':dict(params=[['x','U64']],result='U64',recursive=None,body=body)}}}
    return objects,p.call(str(depth),[{'U64':1}])


class NormalCallCache(unittest.TestCase):
    def test_shared_helper_dag_does_not_repeat_exponential_unfolding(self):
        objects,term=chain(16);saved=copy.deepcopy((objects,term))
        with patch.object(p,'sub',wraps=p.sub)as substitute:
            self.assertEqual(p.normal(term,objects),{'U64':1<<16})
            self.assertLess(substitute.call_count,512)
        self.assertEqual((objects,term),saved)

    @patch.object(p._CallCache,'WARMUP_CALLS',0)
    def test_definitions_arguments_and_modes_cannot_leak_between_invocations(self):
        objects,term=chain(2)
        self.assertEqual(p.normal(term,objects),{'U64':4})
        objects['0']['payload']['declaration']['Function']['body']={'U64':3}
        self.assertEqual(p.normal(term,objects),{'U64':12})
        self.assertEqual(p.normal(p.call('2',[{'U64':7}]),objects),{'U64':12})
        objects,_=chain(2)
        self.assertEqual(p.normal(p.call('2',[{'U64':7}]),objects),{'U64':28})
        self.assertEqual(p.normal(term,objects,opaque=['2']),term)
        self.assertEqual(p.normal(term,objects,blocked=['2']),term)
        self.assertEqual(p.normal(term,objects),{'U64':4})

    @patch.object(p._CallCache,'WARMUP_CALLS',0)
    def test_depth_failure_and_unselected_branch_behavior_are_preserved(self):
        objects,term=chain(3)
        with self.assertRaisesRegex(ValueError,'depth budget'):p.normal(term,objects,depth=95)
        # Calls reached deeper in the same normalization cannot reuse a result
        # computed with more remaining depth.
        deep=copy.deepcopy(term)
        for _ in range(93):deep=p.binary('+',{'U64':0},deep)
        with self.assertRaisesRegex(ValueError,'depth budget'):
            p.normal(p.binary('+',term,deep),objects)
        bad=p.call('missing',[])
        self.assertEqual(p.normal(p.choice({'Bool':True},{'U64':9},bad),objects),{'U64':9})
        recursive={'payload':{'declaration':{'Function':dict(params=[],result='U64',recursive=None,body=p.call('cycle',[]))}}}
        with self.assertRaisesRegex(ValueError,'depth budget'):p.normal(p.call('cycle',[]),{'cycle':recursive})

    def test_cache_is_bounded_and_does_not_alias_mutable_results(self):
        cache=p._CallCache();original={'If':dict(condition=p.var('x'),on_true={'U64':1},on_false={'U64':2})}
        key=cache.key('f',[],0);cache.put(key,original);original['If']['on_true']['U64']=8
        first=__import__('json').loads(cache.get(key));first['If']['on_true']['U64']=17
        self.assertEqual(__import__('json').loads(cache.get(key))['If']['on_true'],{'U64':1})
        for i in range(10000):cache.put(cache.key('f',[{'U64':i}],0),{'U64':i})
        self.assertLessEqual(len(cache.entries),cache.MAX_ENTRIES);self.assertLessEqual(cache.bytes,cache.MAX_BYTES)
        self.assertIsNone(cache.key('f',[{'Var':'x'*100000}],0))
        self.assertIsNone(cache.key('f',[('tuple',)],0))


if __name__=='__main__':unittest.main()
