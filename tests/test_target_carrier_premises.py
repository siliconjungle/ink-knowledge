"""Exact shared-carrier lookup equality remains independently replayable."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical


class TargetCarrierPremises(unittest.TestCase):
    def test_portable_exact_source_equality(self):
        root = Path(__file__).resolve().parents[2]
        compiler = Path(os.environ.get('INK_COMPILER', root / 'target/debug/ink'))
        directory = root / 'knowledge/libraries/proofs/target-carrier-encoded-step'
        store = Store(directory)
        roots = list(json.loads((directory / 'store/names.json').read_text()).values())
        with tempfile.TemporaryDirectory() as temp:
            view = Path(temp) / 'view.json'
            view.write_bytes(canonical(store.bundle(roots)))
            result = subprocess.run([compiler, 'knowledge-check', directory / 'checked-source.json', view],
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)['status'], 'checked')
            stop = root / 'knowledge/libraries/proofs/target-carrier-stop'
            stop_store=Store(stop);ids=list(json.loads((stop/'store/names.json').read_text()).values());view.write_bytes(canonical(stop_store.bundle(ids)))
            result=subprocess.run([compiler,'knowledge-check',stop/'checked-source.json',view],capture_output=True,text=True,timeout=120);self.assertEqual(result.returncode,0,result.stderr)
            source=(root/'examples/crdts/target_carrier_projection.ink').read_text().replace('../../knowledge/libraries/',str(root/'knowledge/libraries')+'/')
            source=source.replace('index:p.index+1,end:p.end','index:p.index+2,end:p.end')
            bad=Path(temp)/'bad.ink';bad.write_text(source);core=Path(temp)/'bad.json'
            result=subprocess.run([compiler,'emit-core',bad,'-o',core],capture_output=True,text=True,timeout=120);self.assertEqual(result.returncode,0,result.stderr)
            result=subprocess.run([os.environ.get('INK_PYTHON','python3'),root/'tools/source_pair_equality.py','--compiler',compiler,'--core',core,'--left','encoded_projected_step','--right','encoded_step_projected','--limit','256','-o',Path(temp)/'false-proof'],capture_output=True,text=True,timeout=120)
            self.assertNotEqual(result.returncode,0);self.assertFalse((Path(temp)/'false-proof').exists())


if __name__ == '__main__':
    unittest.main()
