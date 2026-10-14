import json,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store
from ink_knowledge.store import entry
from ink_knowledge.recipes import load,coverage,indexed_coverage,role
from producers.collection_analysis import analyse
from producers.planning_recipes import lexical_reads,author

class RegistryCoverage(unittest.TestCase):
    def test_index_coverage_matches_audit_and_authenticates_active_ids(self):
        import sqlite3
        objects=[entry(k,s,dict(index=i,node={'Op':['shared-operation',[]]}))
                 for i in range(60) for k,s in [('maintenance','maintenance-test'),
                 ('definition','total-scalar-equality-v1'),('rewrite','ink-conditional-laws-v1')]]
        with tempfile.TemporaryDirectory() as d:
            store=Store.publish(d,objects);store.rebuild()
            expected=coverage(store);actual=indexed_coverage(Store(d))
            for key in ['snapshot','entries','roles','operations','unhandled']:
                self.assertEqual(actual[key],expected[key])
            # An indexed row outside the exact pin must not enter role sets.
            extra=entry('maintenance','maintenance-test',dict(node={'Op':['outside-pin',[]]}))
            store.extend([extra]).refresh_index()
            self.assertEqual(indexed_coverage(Store(d,store.data/'snapshots'/f'{store.snapshot_id}.json'))['operations'],expected['operations'])
            with sqlite3.connect(Path(d)/'index.sqlite') as db,db:
                db.execute('DELETE FROM members WHERE snapshot_id=? AND entry_id=(SELECT entry_id FROM members WHERE snapshot_id=? LIMIT 1)',(store.snapshot_id,store.snapshot_id))
            with self.assertRaisesRegex(ValueError,'membership differs'):
                indexed_coverage(Store(d,store.data/'snapshots'/f'{store.snapshot_id}.json'))

    def test_registry_covers_every_current_operation_kind_and_fails_new_semantics(self):
        families={('rewrite','ink-conditional-laws-v1'),('rewrite','ink-general-laws-v1'),('representation','ink-source-representation-v1'),
            ('implementation','ink-implementation-candidate-v1'),('bridge','ink-representation-migration-v1'),
            ('maintenance','maintenance-test'),('definition','first-order-inductive-equality-v1'),
            ('theorem','first-order-inductive-equality-v1'),('definition','total-scalar-equality-v1'),
            ('definition','ink-target-work-measurement-v1'),('definition','ink-target-work-prices-v1'),
            ('definition','ink-target-work-publication-context-v1'),('definition','ink-source-read-capability-v1'),('definition','ink-source-column-map-v1')}
        objects=[entry(k,s,dict(node={'Op':['new-operation',[]]}))for k,s in families]
        with tempfile.TemporaryDirectory()as d:
            store=Store.publish(d,objects);report=coverage(store)
            self.assertEqual(report['entries'],len(objects));self.assertIn('new-operation',report['operations']);self.assertFalse(report['unhandled'])
        with self.assertRaises(ValueError):role(dict(kind='definition',semantics='unhandled-domain'))
    def test_new_installed_recipe_needs_no_planner_dispatch_change(self):
        registry,_=load()
        self.assertGreater(len(registry['recipes']),30)
        with tempfile.TemporaryDirectory()as d:
            p=Path(d)/'registry.json';registry['recipes'].append(dict(id='new-family',stage='representation',module='producers.new_family',function='generate',parameters={}))
            p.write_text(json.dumps(registry));loaded,_=load(p)
            self.assertEqual(loaded['recipes'][-1]['id'],'new-family')
            registry['recipes'][-1]['module']='os';p.write_text(json.dumps(registry))
            with self.assertRaises(ValueError):load(p)

    def test_published_maintained_fold_is_an_untrusted_candidate(self):
        from producers.planning_recipes import published
        source='a'*64
        package=dict(schema=1,semantics='ink-maintained-fold-v1',input_core_sha256=source,knowledge={},views=[])
        with tempfile.TemporaryDirectory()as d:
            store=Store.publish(d,[entry('maintenance','ink-maintained-fold-v1',dict(package=package))]);store.refresh_index()
            rows=list(published(dict(knowledge_root=d,knowledge_snapshot=store.snapshot_id,source=source)))
            self.assertEqual(len(rows),1)
            self.assertEqual(rows[0]['step'],dict(kind='maintained',package=package))
            self.assertEqual(list(published(dict(knowledge_root=d,knowledge_snapshot=store.snapshot_id,source='b'*64))),[])

    def test_every_public_layout_parameter_has_a_registry_recipe(self):
        import inspect
        from producers.representations import generate
        registry,_=load();recipes=[r['parameters']for r in registry['recipes']if r['function']=='representations']
        covered={k for recipe in recipes for k in recipe}
        # Whole-action replacements are composed by the graph; authoring model
        # and temporary output paths are plumbing, not layout strategies.
        # Access descriptions are recomputed by their source-bound recipe.
        expected=set(inspect.signature(generate).parameters)-{'model','directory','replacement','access'}
        self.assertEqual(covered,expected)
        self.assertTrue(any(r['function']=='point_access_cache' and r['inputs']==['core','model'] for r in registry['recipes']))
    def test_all_other_authoring_parameters_have_recipe_domains(self):
        import inspect
        from producers import generic_indexed,partition_representation,packed_representations,source_sequence_tree,scalar_representation
        registry,_=load()
        for name,module in [('generic_index',generic_indexed),('partition',partition_representation),('packed',packed_representations),('sequence_tree',source_sequence_tree),('scalar',scalar_representation)]:
            expected=set(inspect.signature(module.generate).parameters)-{'model','directory','compiler'}
            actual={k for r in registry['recipes']if r['function']==name for k in r['parameters']}
            self.assertEqual(actual,expected,name)
    def test_physical_strategy_domains_are_published_as_data(self):
        registry,_=load();recipe=next(r for r in registry['recipes']if r['function']=='physical')
        self.assertEqual({r['tables']for r in recipe['parameters']['source_strategies']},{'ordered','indexed_slots'})
        self.assertEqual({r['site_field']for r in recipe['parameters']['definition_strategies']},{'packed_datatypes','memo_functions'})
        self.assertTrue(all('eligible'in r for r in recipe['parameters']['definition_strategies']))
        self.assertEqual({r['buffers']for r in recipe['parameters']['source_strategies']},{'scoped','direct'})
        self.assertTrue(any(r['id']=='source-capabilities'for r in registry['recipes']))

    def test_published_recipe_is_discovered_without_planner_dispatch(self):
        recipe=dict(id='published-family',stage='representation',module='producers.planning_recipes',function='representations',parameters={'retain_queries':False},requires=['model'],obligations=['universal-source-action-and-observation-preservation'])
        with tempfile.TemporaryDirectory()as directory:
            store=Store.publish(directory,[entry('definition','ink-planning-recipes-v1',dict(recipe=recipe))]);store.refresh_index()
            before=load()[1];registry,digest=load(store=store)
            self.assertIn(recipe,registry['recipes']);self.assertNotEqual(before,digest)
            self.assertEqual(coverage(store)['roles']['recipe-discovery'],1)

class ExternalAnalysis(unittest.TestCase):
    def test_let_retains_body_captures_and_nested_lambdas_shadow_outer_names(self):
        p=self.program();f=p['functions'][0]
        f['params'] += [['ys',{'List':'U32'}],['x','U32'],['offset','U32']]
        f['body']={'Let':['local',{'List':'U32'},{'Var':'xs'},{'Var':'ys'}]}
        facts=analyse(p,'mapped')
        self.assertEqual(facts['captures'],['xs','ys'])
        self.assertEqual(facts['aliases'],['ys'])
        f['body']={'Method':[{'Var':'xs'},'map',[{'Lambda':['i',{'Lambda':['x',{'Binary':['+',{'Var':'x'},{'Var':'offset'}]}]}]}]]}
        facts=analyse(p,'mapped')
        self.assertEqual(facts['captures'],['offset','xs'])

    def test_pure_source_does_not_spend_stateful_representation_search_budget(self):
        context=dict(core=dict(program=dict(states=[],actions=[],functions=[])))
        def unexpected(*args):
            self.fail('state representation author called for a pure-only source')
        rows=list(author(context,{},unexpected))
        self.assertEqual(len(rows),1)
        self.assertEqual(rows[0]['status'],'declined')
        self.assertIn('source-function equality',rows[0]['reason'])

    def program(self):
        return dict(records={},functions=[dict(name='mapped',params=[['xs',{'List':'U32'}]],result={'List':'U32'},body={'Method':[{'Var':'xs'},'map',[{'Lambda':['x',{'Var':'x'}]}]]})])
    def test_length_is_an_authoring_hint_not_compiler_authority(self):
        p=self.program();facts=analyse(p,'mapped')
        self.assertEqual(facts['length'],['input','xs']);self.assertEqual(facts['ownership'],'fresh')
        self.assertIn('mathematical certificates required',facts['scope'])
        p['functions'][0]['body']['Method'][1]='filter'
        self.assertIsNone(analyse(p,'mapped')['length'])
    def test_recursion_and_work_limits_do_not_invent_alias_or_length_facts(self):
        p=self.program();p['functions'][0]['body']={'Call':['mapped',[{'Var':'xs'}]]}
        self.assertIsNone(analyse(p,'mapped')['length'])
        self.assertTrue(analyse(p,'mapped',node_budget=0)['exhausted'])
    def test_lexical_place_discovery_does_not_select_scalar_callback_variables(self):
        from ink_knowledge import identity
        sites=lexical_reads(self.program())
        self.assertIn(identity({'Var':'xs'}),sites)
        self.assertNotIn(identity({'Var':'x'}),sites)

if __name__=='__main__':unittest.main()
