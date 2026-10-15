"""Source semantics and CNF encoding are explicit, orthogonal proof inputs."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from producers.author_word_identities import checked_law
from producers.semantic_laws import value,var,word,op
from producers.v8_word_laws import templates


class SourceBitEncodings(unittest.TestCase):
    def test_legacy_and_shared_factory_paths_and_unknown_modes(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        with tempfile.TemporaryDirectory()as tmp:
            d=Path(tmp);source=d/'source.ink';core=d/'core.json'
            source.write_text('module bit_modes;fn identity(x:u32)->u32{return x;}')
            subprocess.run([str(compiler),'emit-core',str(source),'-o',str(core)],check=True,capture_output=True)
            s=value('U32');x=var(s,'x')
            legacy=dict(params={'x':s},conditions=[],**{'from':op(s,'binary:+',x,word('U32',0)),'to':x})
            for encoding in ['literal-v1','shared-v2']:
                case=d/encoding;case.mkdir()
                law,_=checked_law(compiler,core,legacy,case,10,encoding=encoding)
                proof=law['proof']['BitVector']
                self.assertNotIn('semantics',proof)
                self.assertEqual(proof['certificate'].get('encoding','literal-v1'),encoding)
            case=d/'rotated';case.mkdir()
            goal=next(r['goal']for r in templates()if r['name']=='u32/rotate_left_or')
            law,_=checked_law(compiler,core,goal,case,10,semantics='fixed-words-v2',encoding='shared-v2')
            self.assertEqual(law['proof']['BitVector']['semantics'],'fixed-words-v2')
            self.assertEqual(law['proof']['BitVector']['certificate']['encoding'],'shared-v2')
            request=d/'goal.json';request.write_text(json.dumps(legacy))
            for flag in ['--semantics','--encoding']:
                result=subprocess.run([str(compiler),'semantic-bitvector-obligation',str(core),str(request),'--core',flag,'unknown','-o',str(d/'cnf.json')],capture_output=True,text=True)
                self.assertNotEqual(result.returncode,0)
                self.assertIn('unknown',result.stderr)


if __name__=='__main__':unittest.main()
