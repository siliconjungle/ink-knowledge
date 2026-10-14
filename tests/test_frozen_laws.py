import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from ink_knowledge import canonical
from producers import frozen_laws
from producers.semantic_laws import value,var


class IndexedProofLibraries(unittest.TestCase):
    def test_partial_acquisition_preserves_old_index_and_all_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);x=var(value('U32'),'x')
            law=dict(params={'x':value('U32')},**{'from':x,'to':x},proof='Normalize')
            self.assertEqual(frozen_laws.update(d,[dict(name='first',law=law)]),1)
            saved=d/'prior.json';os.link(d/'index.json',saved);original=saved.read_bytes()
            self.assertEqual(frozen_laws.update(d,[dict(name='second',law=law)]),2)
            self.assertEqual(saved.read_bytes(),original)
            self.assertEqual([r['name'] for r in frozen_laws.read(d)],['first','second'])
            self.assertEqual(frozen_laws.update(d,[]),2)

    def test_unmatched_proofs_are_not_opened_and_tampered_metadata_rejects(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);x=var(value('U32'),'x')
            law=dict(params={},**{'from':x,'to':x},proof='Normalize')
            frozen_laws.update(d,[dict(name='word',law=law)])
            with patch.object(frozen_laws,'load',side_effect=AssertionError('unmatched proof loaded')):
                self.assertEqual(frozen_laws.specialize({'functions':{'f':var(value('Bool'),'b')}},d,'test/'),[])
            packet=json.loads((d/'index.json').read_bytes())
            packet['rows'][0]['from']=var(value('U32'),'different')
            (d/'index.json').write_bytes(canonical(packet))
            with self.assertRaisesRegex(ValueError,'index/proof mismatch'):
                frozen_laws.read(d)
            packet['rows'][0]['sha256']='../'+'a'*61
            (d/'index.json').write_bytes(canonical(packet))
            with self.assertRaisesRegex(ValueError,'index row'):
                frozen_laws.read(d)

    def test_corrupted_proof_cannot_be_replaced_silently(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);x=var(value('U32'),'x')
            row=dict(name='word',law=dict(params={},**{'from':x,'to':x},proof='Normalize'))
            frozen_laws.update(d,[row]);meta=frozen_laws.index(d)[0]
            path=d/(meta['sha256']+'.json.gz')
            import gzip
            path.write_bytes(gzip.compress(b'{}'))
            with self.assertRaisesRegex(ValueError,'content mismatch'):
                frozen_laws.update(d,[row])
            with self.assertRaisesRegex(ValueError,'index/proof mismatch'):
                frozen_laws.read(d)
