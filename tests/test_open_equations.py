"""Live captures remain opaque while small universal reductions compose."""
import copy
import gzip
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, canonical
from producers.fold_chunks import FoldChunks, compose
from producers.open_equations import OpenEquations

ROOT = Path(__file__).resolve().parents[2]
INK = Path(os.environ.get('INK_COMPILER', ROOT/'target/debug/ink')).resolve()


class OpenComputation(unittest.TestCase):
    def test_network_conversion_uses_factored_definitions_and_rejects_altered_error(self):
        fixture = Path(__file__).parent/'fixtures/open-equation-conversion.json.gz'
        wire = json.loads(gzip.decompress(fixture.read_bytes()))
        original = wire['objects'][wire['roots'][0]]['payload']['declaration']['Theorem']
        chunks = FoldChunks(wire['objects'], [])
        chunks.gates = {key for key, obj in chunks.objects.items()
            if (f := obj['payload'].get('declaration', {}).get('Function'))
            and f['recursive'] is not None and key not in chunks.folds and chunks.acyclic(key)}
        author = OpenEquations(chunks)
        left, first = author.normalize(original['from'], dict(original['params']))
        right, second = author.normalize(original['to'], dict(original['params']))
        proof = compose([first, author.closed.conversion(left, right), {'Sym': second}])
        # Error text is part of the complete mathematical result, too. Rehashing
        # a same-typed changed endpoint must not preserve proof authority.
        changed = copy.deepcopy(original['to'])
        pending = [changed['If']['on_true']]
        while pending:
            node = pending.pop()
            if isinstance(node, dict):
                if 'U64' in node:
                    node['U64'] ^= 1
                    break
                pending.extend(reversed(list(node.values())))
            elif isinstance(node, list):
                pending.extend(reversed(node))
        else:
            self.fail('missing error text word')
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder/'source.ink'; core = folder/'source.json'
            source.write_text('module open_computation;fn f(x:u32)->u32{return x;}')
            subprocess.run([INK, 'emit-core', source, '-o', core], check=True, capture_output=True)
            for good, target in [(True, original['to']), (False, changed)]:
                key = chunks.theorem(original['params'], original['from'], target, proof)
                store = Store.publish(folder/str(good), list(chunks.objects.values()))
                view = folder/('view-'+str(good)+'.json')
                view.write_bytes(canonical(store.bundle([key])))
                result = subprocess.run([INK, 'knowledge-check', core, view], capture_output=True,
                                        text=True, timeout=180)
                self.assertEqual(result.returncode == 0, good, result.stderr[-3000:])
        self.assertLess(chunks.work, 100_000)


if __name__ == '__main__':
    unittest.main()
