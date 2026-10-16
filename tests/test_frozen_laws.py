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

    def test_installed_catalogues_return_exact_exhaustive_rows_before_loading(self):
        from ink_planner.semantic_search import positions, match
        from producers.semantic_laws import op, word
        root=Path(__file__).resolve().parents[1]
        # Renamed positive sites and unrelated arithmetic, with nested sites and
        # duplicate values, exercise all installed metadata without opening RUP.
        for directory in sorted((root/'producers/data').glob('*/index.json')):
            rows=frozen_laws.index(directory.parent)
            def renamed(t):
                if isinstance(t,dict):
                    return {k:('renamed_'+v if k=='Free'else renamed(v))for k,v in t.items()}
                if isinstance(t,list):return [renamed(v)for v in t]
                return t
            bodies={str(i):renamed(row['from'])for i,row in enumerate(rows[::17])}
            bodies['unrelated']=op(value('U64'),'binary:+',word('U64',11),word('U64',13))
            subject=dict(functions=bodies)
            sites=[t for body in bodies.values()for _,t in positions(body)]
            expected=[('prefix/'+row['name'],row['sha256'])for row in rows
                      if any(match(row['from'],t,row['params'],{})for t in sites)]
            with patch.object(frozen_laws,'load',side_effect=AssertionError('metadata opened a proof')):
                selected=frozen_laws.matching_rows(subject,rows)
                self.assertEqual([('prefix/'+row['name'],row['sha256'])for row in selected],expected)
            # V2 may additionally load explicit supporting witnesses, exercised
            # by the dependency tests. V1 keeps the exact former load behavior.
            if json.loads(directory.read_bytes())['schema']!=1:
                continue
            with patch.object(frozen_laws,'load',side_effect=lambda _,row:row['sha256'])as loader:
                self.assertEqual(frozen_laws.specialize(subject,directory.parent,'prefix/'),expected)
                self.assertEqual(loader.call_count,len(expected))
