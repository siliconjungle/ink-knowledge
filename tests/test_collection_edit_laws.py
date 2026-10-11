"""General edit identities are data; hashes and producers confer no authority."""
import json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,semantic_entry
from ink_knowledge.proposals import generate
from producers.collection_edit_laws import named_laws,specialize
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))

class CollectionEditLaws(unittest.TestCase):
    def test_all_carriers_nominal_discovery_and_false_identity_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            d=Path(directory);core=d/'core.json';subject=d/'subject.json';view=d/'view.json'
            def run(*args): return subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True)
            for args in [('emit-core',ROOT/'examples/collection-edits.ink','-o',core),('emit-semantic',core,'--core','-o',subject)]:
                r=run(*args);self.assertEqual(r.returncode,0,r.stderr)
            rows=named_laws();self.assertEqual(len(rows),24)
            st=Store.publish(d/'portable',[semantic_entry(l) for _,l in rows]);view.write_bytes(canonical(st.bundle(list(st.members())))+b'\n')
            r=run('knowledge-check',core,view);self.assertEqual(r.returncode,0,r.stderr)
            s,c=json.loads(subject.read_text()),json.loads(core.read_text())
            generated=specialize(s,c);self.assertEqual(len(generated),12)
            objects,receipts=generate(s,c)
            nominal=[o for o in objects.values() if o['payload'].get('definition_context',{}).get('records') and 'GeneralizedInduction' in o['payload']['proof']]
            self.assertEqual(len(nominal),3)
            st=Store.publish(d/'nominal',nominal);view.write_bytes(canonical(st.bundle(list(st.members())))+b'\n')
            r=run('knowledge-check',core,view);self.assertEqual(r.returncode,0,r.stderr)
            # Retaining the first write is false; publish with fresh genuine
            # hashes so rejection tests mathematics rather than content IDs.
            bad=json.loads(json.dumps(rows[0][1]))
            bad['to']['node']['Op'][1][0]['node']['Op'][1][2]=bad['from']['node']['Op'][1][0]['node']['Op'][1][0]['node']['Op'][1][2]
            st=Store.publish(d/'false',[semantic_entry(bad)]);view.write_bytes(canonical(st.bundle(list(st.members())))+b'\n')
            r=run('knowledge-check',core,view);self.assertNotEqual(r.returncode,0);self.assertNotIn('hash mismatch',r.stderr)

if __name__=='__main__':unittest.main()
