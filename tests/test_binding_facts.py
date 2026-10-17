"""Shared syntax retains lexical scope and opt-in constructor exposure."""
import copy
import random
import unittest
from unittest.mock import patch

from producers import point_delta as p


def reference(value, bound=frozenset()):
    if isinstance(value, list):
        pairs = [reference(v, bound) for v in value]
    elif isinstance(value, dict):
        if set(value) == {'Var'}:
            return ({value['Var']} - set(bound)), set()
        if 'Match' in value:
            node = value['Match']; pairs = [reference(node['scrutinee'], bound)]
            for branch in node['branches']:
                free, names = reference(branch['body'], bound | set(branch['bindings']))
                pairs.append((free, names | set(branch['bindings'])))
        else:
            pairs = [reference(v, bound) for v in value.values()]
    else:
        return set(), set()
    return (set().union(*(a for a, _ in pairs)), set().union(*(b for _, b in pairs)))


class BindingFacts(unittest.TestCase):
    def test_closed_call_preservation_is_scoped_and_work_is_charged(self):
        objects = {'increment': {'payload': {'declaration': {'Function': dict(
            params=[['value', 'U64']], result='U64', recursive=None,
            body=p.binary('+', p.var('value'), {'U64': 1}))}}}}
        closed = p.call('increment', [{'U64': 4}])
        self.assertEqual(p.normal(closed, objects), {'U64': 5})
        self.assertEqual(p.normal(closed, objects, preserve_closed_calls=True), closed)
        opened = p.call('increment', [p.var('input')])
        self.assertEqual(p.normal(opened, objects, preserve_closed_calls=True),
                         p.binary('+', p.var('input'), {'U64': 1}))
        self.assertEqual(p.normal(closed, objects), {'U64': 5})
        def exhausted():
            raise ValueError('authoring work exhausted')
        with self.assertRaisesRegex(ValueError, 'authoring work exhausted'):
            p.normal(closed, objects, tick=exhausted)

    def test_shared_terms_keep_free_and_bound_occurrences_distinct(self):
        rng = random.Random(719)
        pool = [p.var(n) for n in ['x', 'y', 'z', 'input']]
        for _ in range(160):
            a, b = rng.choices(pool, k=2)
            term = (p.match(a, [([rng.choice(['x', 'y', 'z'])], b)])
                    if rng.randrange(2) else p.binary('+', a, b))
            pool.append(term)
            # Keep the independent tree walk bounded while retaining DAGs.
            if len(pool) > 16: pool.pop(4)
            free, bound = reference(term)
            self.assertEqual(p.free_variables(term), free)
            self.assertEqual(p.binding_names(term), bound)
            self.assertEqual(p.free_variables(term, {'x'}), free - {'x'})

    def test_summary_exhaustion_and_later_mutation_do_not_change_substitution(self):
        argument = p.match(p.var('other'), [(['x'], p.var('x'))])
        term = p.match(p.var('input'), [(['x'], p.binary('+', p.var('x'), p.var('argument')))])
        saved = copy.deepcopy((term, argument))
        expected = p.sub(term, {'argument': argument})
        with patch.object(p._BindingFacts, 'MAX_BYTES', 0):
            self.assertEqual(p.sub(term, {'argument': argument}), expected)
        self.assertEqual((term, argument), saved)
        argument['Match']['branches'][0]['bindings'] = ['fresh']
        self.assertEqual(p.binding_names(argument), {'fresh'})
        self.assertEqual(p.free_variables(argument), {'other', 'x'})

    def test_constructor_heads_are_opt_in_scoped_and_leave_other_fields_opaque(self):
        value = p.cons('pair', 0, [{'U64': 3}, p.call('unknown', [])])
        objects = {'alias': {'payload': {'declaration': {'Function': dict(
            params=[], result={'Data': 'pair'}, recursive=None, body=value)}}},
            'unknown': {'payload': {'declaration': {'AbstractFunction': dict(
                name='unknown', params=[], result='U64')}}}}
        term = p.match(p.call('alias', []), [(['first', 'second'], p.var('first'))])
        saved = copy.deepcopy((term, objects))
        retained = p.normal(term, objects, opaque={'alias'})
        self.assertEqual(p.normal(term, objects, opaque={'alias'}, heads={'alias'}), {'U64': 3})
        self.assertEqual(p.normal(term, objects, opaque={'alias'}), retained)
        self.assertEqual((term, objects), saved)
        objects['alias']['payload']['declaration']['Function']['body']['Construct']['arguments'][0] = {'U64': 4}
        self.assertEqual(p.normal(term, objects, opaque={'alias'}, heads={'alias'}), {'U64': 4})

    def test_large_borrowed_dag_uses_summaries_after_retained_cache_is_full(self):
        # Fill the retained cache before a deeply shared continuation. A tree
        # walk of the continuation would exceed the explicit work allowance.
        prefix = [p.var('prefix_'+str(i)) for i in range(5000)]
        shared = p.var('input')
        for _ in range(30):
            shared = p.binary('+',shared,shared)
        term = [prefix,shared]
        with patch.object(p._BindingFacts,'MAX_WORK',50_000):
            self.assertEqual(p.free_variables(term),{'input'}|{v['Var'] for v in prefix})
        with patch.object(p._BindingFacts,'MAX_LOCAL_BYTES',0), patch.object(p._BindingFacts,'MAX_WORK',50_000):
            with self.assertRaisesRegex(ValueError,'binding facts resource limit'):
                p.free_variables(term)
        # A caller mutation cannot reuse the previous walk's borrowed facts.
        shared['Binary']['right']=p.var('changed')
        self.assertIn('changed',p.free_variables(term))

    def test_substitution_reuses_its_exact_large_input_summary_across_binders(self):
        argument = [p.var('input_'+str(i)) for i in range(3000)]
        term = [p.match(p.var('tag'),[(['local'],p.var('argument'))]) for _ in range(100)]
        # A fresh analysis of the same capture at every binder would exceed
        # this total allowance; its borrowed summary is computed once.
        with patch.object(p._BindingFacts,'MAX_WORK',30_000):
            result=p.sub(term,{'argument':argument})
        self.assertIs(result[0]['Match']['branches'][0]['body'],argument)
        with patch.object(p._BindingFacts,'MAX_WORK',1):
            with self.assertRaisesRegex(ValueError,'resource limit'):
                p.sub(term,{'argument':argument})

    def test_constructor_head_alias_cycles_fail_boundedly(self):
        definition = lambda body: {'payload': {'declaration': {'Function': dict(
            params=[], result={'Data': 'pair'}, recursive=None, body=body)}}}
        objects = {'a': definition(p.call('b', [])), 'b': definition(p.call('a', []))}
        term = p.match(p.call('a', []), [([], {'U64': 0})])
        with self.assertRaisesRegex(ValueError, 'depth/cycle'):
            p.normal(term, objects, opaque={'a', 'b'}, heads={'a', 'b'})
