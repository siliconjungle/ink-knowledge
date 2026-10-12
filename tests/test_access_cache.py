import copy
import unittest
from producers.access_cache import discover, decisions


def fixture():
    point = dict(root='Items', mode='read', scope={'Point':dict(key_type='U64',key={'Number':0})}, conditions=[])
    write = {**point,'mode':'write','scope':{'Point':dict(key_type='U64',key={'Parameter':0})}}
    summaries = {
        'watched':dict(kind='Query',parameters=[],accesses=[point]),
        'edit':dict(kind='Change',parameters=[['key','U64']],accesses=[write]),
        'scan':dict(kind='Query',parameters=[],accesses=[{**point,'scope':{'Whole':{'reason':'scan'}}}]),
        'unknown':dict(kind='Change',parameters=[],accesses=[{**write,'scope':{'Whole':{'reason':'state-derived key'}}}]),
    }
    return dict(source='1'*64,actions=dict.fromkeys(summaries)),dict(
        schema=1,semantics='ink-action-access-v1',source='1'*64,actions=summaries)


class AccessCacheTests(unittest.TestCase):
    def test_discovery_and_fallback_explanations(self):
        model,access=fixture()
        self.assertEqual(discover(model,access),['watched'])
        choices=decisions(model,access,'watched')
        self.assertTrue(choices['edit']['eligible'])
        self.assertFalse(choices['unknown']['eligible'])
        self.assertIn('refresh fallback',choices['unknown']['reason'])
        self.assertFalse(choices['scan']['eligible'])

    def test_source_and_coverage_mismatch_decline(self):
        model,access=fixture()
        for bad in [dict(access,source='2'*64),dict(access,actions={})]:
            with self.assertRaises(ValueError):discover(model,bad)

    def test_conditional_multiple_root_and_parameter_queries_decline(self):
        model,access=fixture()
        for kind in ['condition','root','parameter','unknown']:
            bad=copy.deepcopy(access);query=bad['actions']['watched']
            if kind=='condition':query['accesses'][0]['conditions']=[dict(expression={'Bool':True},value=True)]
            if kind=='root':query['accesses'].append({**query['accesses'][0],'root':'Other'})
            if kind=='parameter':query['parameters']=[['key','U64']]
            if kind=='unknown':query['accesses'][0]['scope']={'Whole':{'reason':'unknown'}}
            self.assertNotIn('watched',discover(model,bad))


if __name__=='__main__':unittest.main()
