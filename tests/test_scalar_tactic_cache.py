"""Proof-cache entries cannot survive a change to the checker at the same path."""
import hashlib
import json
import os
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from producers.scalar_tactic import Scalar


class ScalarCache(unittest.TestCase):
    def test_reuses_same_checker_but_reauthors_after_checker_changes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            compiler = root / 'ink'
            compiler.write_bytes(b'checker revision one')
            calls = []
            theorems = []

            def run(arguments, **kwargs):
                calls.append(arguments)
                Path(arguments[-1]).write_text(json.dumps({
                    'sha256': hashlib.sha256(compiler.read_bytes()).hexdigest(),
                    'clauses': [[]],
                }))
                return SimpleNamespace(returncode=0, stderr='')

            def add(theorem):
                theorems.append(theorem)
                return str(len(theorems))

            def prove():
                scalar = Scalar(add, lambda term, env: 'Bool', lambda term, env: term)
                scalar.prove({'Var': 'x'}, {'Bool': True}, {'x': 'Bool'})
                return theorems[-1]['Theorem']['proof']['BitVector']['certificate']['problem_sha256']

            with patch.dict(os.environ, INK_COMPILER=str(compiler)), \
                 patch('producers.scalar_tactic.__file__', str(root/'producers/scalar_tactic.py')), \
                 patch('producers.scalar_tactic.subprocess.run', side_effect=run), \
                 patch('producers.scalar_tactic.certificate', side_effect=lambda problem, **kw: {
                     'problem_sha256': problem['sha256'], 'steps': [{'clause': [], 'hints': [0]}],
                 }):
                first = prove()
                self.assertEqual(prove(), first)
                self.assertEqual(len(calls), 1)
                compiler.write_bytes(b'checker revision two')
                self.assertNotEqual(prove(), first)
                self.assertEqual(len(calls), 2)
