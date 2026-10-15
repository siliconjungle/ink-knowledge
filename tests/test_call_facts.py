"""Call summaries are scoped suggestions; whole equations need independent replay."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from producers.call_facts import expand
from producers.conditional_facts import acquire
from producers.semantic_laws import op,var,value,word
from ink_knowledge import canonical

class CallFacts(unittest.TestCase):
    def test_bounded_substitution_preserves_scope_and_invalidates_on_changed_definition(self):
        u=value('U32');x=var(u,'x');body=op(u,'binary:+',var(u,'arg'),word('U32',3))
        core={'program':{'functions':[dict(name='helper',params=[['arg','U32']],result='U32')]}}
        subject={'functions':{'helper':body}};source=op(u,'call:helper',x)
        result,receipt=expand(source,core,subject);self.assertEqual(result,op(u,'binary:+',x,word('U32',3)))
        self.assertEqual(receipt['expanded_calls'],1)
        changed=copy.deepcopy(subject);changed['functions']['helper']['node']['Op'][1][1]=word('U32',4)
        other,new=expand(source,core,changed);self.assertNotEqual(result,other);self.assertNotEqual(receipt['definitions'],new['definitions'])
        recursive={'functions':{'helper':op(u,'call:helper',var(u,'arg'))}}
        with self.assertRaisesRegex(ValueError,'recursive'):expand(source,core,recursive)
        for budget in [0,1,2]:
            with self.assertRaises(ValueError):expand(source,core,subject,max_nodes=budget)
        # Repeated arguments must be bounded before materialising expansions.
        doubled={'functions':{'helper':op(u,'binary:+',var(u,'arg'),var(u,'arg'))}}
        source=x
        for _ in range(16):source=op(u,'call:helper',source)
        with self.assertRaises(ValueError):expand(source,core,doubled,max_nodes=64)

    def test_whole_call_laws_replay_and_stale_contexts_reject(self):
        compiler=Path(os.environ['INK_COMPILER']).resolve()
        source=Path(__file__).parent/'fixtures/call-facts/source.ink'
        with tempfile.TemporaryDirectory()as tmp:
            d=Path(tmp);packet,receipt=acquire(source,compiler,d,seconds=60)
            self.assertEqual({a['function']for a in packet['applications']},{'bounded','observed'})
            self.assertTrue(all(a.get('call_summary',{}).get('expanded_calls',0)>0 for a in receipt['attempts']if a['status']=='checked'))
            old=d/'selection.json';changed=d/'changed.ink';changed.write_text(source.read_text().replace('return value+3','return value+4'))
            run=subprocess.run([str(compiler),'emit-core',str(changed),'-o',str(d/'changed.json')],capture_output=True,text=True);self.assertEqual(run.returncode,0,run.stderr)
            forged=copy.deepcopy(packet)
            semantic=d/'changed-semantic.json';run=subprocess.run([str(compiler),'emit-semantic',str(d/'changed.json'),'--core','-o',str(semantic)],capture_output=True,text=True);self.assertEqual(run.returncode,0,run.stderr)
            forged['input_core_sha256']=json.loads(semantic.read_bytes())['input_core_sha256']
            old.write_bytes(canonical(forged));run=subprocess.run([str(compiler),'check-selection',str(d/'changed.json'),str(old)],capture_output=True,text=True)
            self.assertNotEqual(run.returncode,0,'source rehash must not authorize a stale helper summary')

if __name__=='__main__':unittest.main()
