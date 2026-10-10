import copy
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'knowledge'))
sys.path.insert(0, str(ROOT / 'planner'))
from ink_knowledge import Store, identity, semantic_entry
from ink_planner.definition_context import applicable, applicable_roots
from ink_planner.semantic_search import search
from producers.definition_context28 import bind, capture
from producers.semantic_laws import law, op, value, var, word


class DefinitionContexts(unittest.TestCase):
    def fixture(self):
        s = value('U32'); x = var(s, 'x')
        program = dict(functions=[dict(name=n, params=[['x', 'U32']], result='U32', body=None)
                                  for n in ('leaf', 'helper', 'entry')], records={}, enums={})
        subject = dict(functions=dict(leaf=op(s, 'binary:+', x, word('U32', 1)),
                                      helper=op(s, 'call:leaf', x), entry=op(s, 'call:helper', x)))
        equation = law({'x': s}, subject['functions']['entry'], subject['functions']['leaf'])
        return dict(program=program), subject, equation

    def test_content_closure_storage_and_transitive_prefilter(self):
        core, subject, equation = self.fixture()
        equation = bind(equation, core, subject)
        context = equation['definition_context']
        self.assertEqual(set(context['definitions']), {'leaf', 'helper'})
        leaf = context['definitions']['leaf']
        self.assertEqual(leaf['sha256'], identity(leaf['definition']))
        self.assertEqual(context['definitions']['helper']['definition']['callees'], {'leaf': leaf['sha256']})
        self.assertTrue(applicable(equation, core['program'], subject))
        changed = copy.deepcopy(subject)
        changed['functions']['leaf']['node']['Op'][1][1] = word('U32', 2)
        self.assertFalse(applicable(equation, core['program'], changed))
        for field, new in [('result', 'U64'), ('params', [['y', 'U32']])]:
            changed_core = copy.deepcopy(core)
            changed_core['program']['functions'][0][field] = new
            self.assertFalse(applicable(equation, changed_core['program'], subject))
        missing = copy.deepcopy(core)
        missing['program']['functions'] = missing['program']['functions'][1:]
        self.assertFalse(applicable(equation, missing['program'], subject))
        with tempfile.TemporaryDirectory() as directory:
            obj = semantic_entry(equation)
            store = Store.publish(Path(directory), [obj])
            self.assertEqual(applicable_roots(store, [identity(obj)], core['program'], subject), [identity(obj)])
            self.assertEqual(applicable_roots(store, [identity(obj)], core['program'], changed), [])
            self.assertEqual(store.object(identity(obj))['payload']['definition_context'], context)

    def test_search_visits_private_helpers_and_contextual_dependencies_filter(self):
        core, subject, equation = self.fixture()
        s = value('U32'); x = var(s, 'x')
        direct = law({'x': s}, subject['functions']['leaf'], x)
        # Mocked checker isolates traversal only; this false arithmetic law is
        # rejected by the independent core tests and never installed here.
        ident = identity(semantic_entry(direct))
        apps, receipt = search(subject, dict(roots=[ident], objects={ident: direct}), lambda _: True, 16)
        self.assertEqual(apps[0]['function'], 'leaf')
        self.assertLess(receipt['selected_cost'], receipt['initial_cost'])
        contextual = bind(equation, core, subject)
        obj = semantic_entry(contextual); bound_id = identity(obj)
        derived = law({'x': s}, contextual['from'], contextual['to'],
                      {'Use': dict(law=bound_id, arguments={'x': x}, premises=[])}, dependencies=[bound_id])
        root = semantic_entry(derived)
        with tempfile.TemporaryDirectory() as directory:
            store = Store.publish(Path(directory), [obj, root])
            changed = copy.deepcopy(subject); changed['functions']['leaf'] = word('U32', 0)
            self.assertEqual(applicable_roots(store, [identity(root)], core['program'], changed), [])

    def test_capture_rejects_cycles_and_context_free_bytes_stay_unchanged(self):
        core, subject, equation = self.fixture()
        self.assertNotIn('definition_context', semantic_entry(equation)['payload'])
        subject['functions']['leaf'] = subject['functions']['helper']
        with self.assertRaisesRegex(ValueError, 'cyclic'):
            capture(core, subject, ['helper'])


if __name__ == '__main__':
    unittest.main()
