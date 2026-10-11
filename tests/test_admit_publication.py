"""Canonical publication must not advance a pin when local checking refuses it."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'producers'))
from ink_knowledge import Store
from producers.admit_representations import publish
from producers.state_calculus import CanonicalLibrary

COMPILER=Path(os.environ.get('INK_COMPILER',Path(__file__).resolve().parents[2]/'target/debug/ink'))

class Publication(unittest.TestCase):
    @unittest.skipUnless(COMPILER.is_file(),'requires the independently built checker')
    def test_mathematics_admission_publishes_exact_bytes_and_refusal_preserves_pin(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);source=root/'subject.ink';core=root/'core.json';view=root/'view.json';report=root/'receipt.json'
            source.write_text('module admission;fn identity(x:u64)->u64{return x;}')
            subprocess.run([str(COMPILER),'emit-core',str(source),'-o',str(core)],check=True,capture_output=True)
            lib=CanonicalLibrary();rid=lib.theorem('identity',[['x','U64']],{'Var':'x'},{'Var':'x'},{'Refl':{'Var':'x'}})
            store=Store.publish(root/'store',lib.objects.values(),lib.names)
            initial=store.snapshot_id;view.write_text(json.dumps(store.bundle([rid])))
            receipt=publish(store.root,COMPILER,[],report,[('identity',core,view)])
            self.assertEqual(receipt['status'],'checked');self.assertEqual(receipt['mathematics'][0]['roots'],[rid])
            self.assertEqual(set(Store(store.root,store.data/'snapshots'/f'{initial}.json').members()),{rid})
            pin=Store(store.root).snapshot_id
            bad=CanonicalLibrary();forged=bad.theorem('false',[['x','U64']],{'Var':'x'},{'U64':0},{'Refl':{'Var':'x'}})
            proposal=Store.publish(root/'bad',bad.objects.values(),bad.names);view.write_text(json.dumps(proposal.bundle([forged])))
            with self.assertRaises(RuntimeError):publish(store.root,COMPILER,[],report,[('false',core,view)])
            self.assertEqual(Store(store.root).snapshot_id,pin)

if __name__=='__main__':unittest.main()
