import copy,json,tempfile,unittest
from ink_knowledge import Store,identity,canonical
from producers.pipeline_templates import templates,publish
class PipelineTemplates(unittest.TestCase):
    def test_publication_has_no_source_or_backend_specific_cases(self):
        rows=templates();self.assertEqual(len(rows),18)
        with tempfile.TemporaryDirectory()as d:
            old=Store.publish(d,[],{});new=publish(d)
            self.assertNotEqual(old.snapshot_id,new.snapshot_id)
            self.assertEqual(len(new.query(kind='definition',semantics='ink-semantic-law-template-v1')),18)
            self.assertEqual([r['object']for r in rows],[new.object(identity(r['object']))for r in rows])
        for row in rows:
            payload=row['object']['payload'];self.assertEqual(payload['law']['conditions'],[])
            self.assertEqual(len(payload['dependencies']),1 if row['name']=='foldr-first-option'else 0)
            self.assertNotIn('definition_context',payload['law'])
            self.assertNotIn('F32',str(payload))
