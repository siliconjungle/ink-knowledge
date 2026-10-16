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

    def test_constructor_head_alias_cycles_fail_boundedly(self):
        definition = lambda body: {'payload': {'declaration': {'Function': dict(
            params=[], result={'Data': 'pair'}, recursive=None, body=body)}}}
        objects = {'a': definition(p.call('b', [])), 'b': definition(p.call('a', []))}
        term = p.match(p.call('a', []), [([], {'U64': 0})])
        with self.assertRaisesRegex(ValueError, 'depth/cycle'):
            p.normal(term, objects, opaque={'a', 'b'}, heads={'a', 'b'})
