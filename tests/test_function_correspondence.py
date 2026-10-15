"""Exact normalization cannot be replaced by signatures, hashes or AD names."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from producers.function_correspondence import acquire

class Correspondence(unittest.TestCase):
    def test_admitted_batch_equations_and_changed_contexts(self):
        compiler=Path(os.environ['INK_COMPILER']).resolve()
        source=Path(__file__).parent/'fixtures/differential-batching/source.ink'
        pairs=[('batched','directions'),('nonlinear_batched','nonlinear_directions')]
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp)
            view,receipt=acquire(source,compiler,d/'good',pairs)
            packet=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=receipt['input_core_sha256'],knowledge=view,
                        applications=[dict(function='observed',path=[],law=receipt['equations'][0]['law'],premises=[],
                          arguments={'w':{'sort':{'Value':{'Named':'W'}},'node':{'Free':'w'}},'x':{'sort':{'Value':'F32'},'node':{'Free':'x'}}})])
            selection=d/'selection.json';selection.write_text(json.dumps(packet))
            r=subprocess.run([str(compiler),'check-selection',str(d/'good/core.json'),str(selection)],capture_output=True,text=True)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertEqual(len(receipt['admission']['entries']),2)
            changed=d/'changed.ink'
            changed.write_text(source.read_text().replace('return y*y','return y+y'))
            changed_core=d/'changed.json'
            r=subprocess.run([str(compiler),'emit-core',str(changed),'-o',str(changed_core)],capture_output=True,text=True)
            self.assertEqual(r.returncode,0,r.stderr)
            changed_receipt=json.loads(r.stdout)
            forged=copy.deepcopy(packet);forged['input_core_sha256']=changed_receipt['core_sha256'];selection.write_text(json.dumps(forged))
            r=subprocess.run([str(compiler),'check-selection',str(changed_core),str(selection)],capture_output=True,text=True)
            self.assertNotEqual(r.returncode,0,'rehashing the source must not attach stale definitions')
            changed.write_text(source.read_text().replace('a:1.0,b:0.0','a:0.0,b:0.0'))
            with self.assertRaises(ValueError):
                acquire(changed,compiler,d/'wrong',pairs)
            with self.assertRaises(ValueError):
                acquire(source,compiler,d/'signature',[('polynomial','batched')])
            with self.assertRaises(ValueError):
                acquire(source,compiler,d/'duplicate',[pairs[0],pairs[0]])

if __name__=='__main__':unittest.main()
