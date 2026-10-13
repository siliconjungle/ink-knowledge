"""False descent and forged authentic evidence fail independent core replay."""
import copy,json,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,entry,identity
from producers.workspace import compiler_path
from producers.termination_measures import produce,SEMANTICS

class TerminationMeasures(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.compiler=compiler_path()
        if not cls.compiler.exists():raise unittest.SkipTest('INK_COMPILER is required')
    def test_false_and_shadowed_descent_are_solver_counterexamples(self):
        for body in [
            'if n>0 {return f(n);}return 0;',
            'return f(n-1);',
            'let n:u32=n+1;if n>0{return f(n-1);}return 0;',
        ]:
            with self.subTest(body=body),tempfile.TemporaryDirectory() as temp:
                root=Path(temp);source=root/'main.ink'
                source.write_text('module invalid;fn f(n:u32)->u32 decreases n;{'+body+'}')
                with self.assertRaisesRegex(ValueError,'counterexample'):produce(source,self.compiler,root/'proofs')
    def test_rehashing_invalid_rup_or_decreasing_claim_does_not_grant_admission(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);source=root/'main.ink'
            source.write_text('module measured;fn f(n:u32,d:u32)->u32 decreases n;{if d>0&&n>=d{return f(n-d,d)+1;}return 0;}')
            bundle,store=produce(source,self.compiler,root/'valid')
            original=store.object(bundle['roots'][0]);bad=copy.deepcopy(original['payload'])
            bad['proof']['steps']=[]
            obj=entry('definition',SEMANTICS,bad);bank=Store.publish(root/'forged',[obj]);packet=root/'forged.json'
            packet.write_text(json.dumps(bank.bundle([identity(obj)])))
            result=subprocess.run([str(self.compiler),'check',str(source),'--termination-proofs',str(packet)],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0);self.assertIn('bit proof',result.stderr)
    def test_mutual_recursion_cannot_hide_behind_authored_annotations(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);source=root/'main.ink'
            source.write_text('module mutual;fn a(n:u32)->u32 decreases n;{if n>0{return a(n-1);}return b(n);}fn b(n:u32)->u32{return a(n);}')
            result=subprocess.run([str(self.compiler),'emit-termination-obligations',str(source),'-o',str(root/'goals.json')],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0);self.assertIn('recursive call',result.stderr)

    def test_lexicographic_components_allow_reset_only_after_a_prior_decrease(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);source=root/'main.ink'
            source.write_text('module lex;fn f(a:u32,b:u32,reset:u32)->u32 decreases [a,b];{if b>0{return f(a,b-1,reset)+1;}if a>0{return f(a-1,reset,reset)+1;}return 0;}')
            bundle,store=produce(source,self.compiler,root/'proofs')
            self.assertEqual(len(bundle['roots']),2)
            # Authenticate a previously checked packet against changed source.
            source.write_text('module lex;fn f(a:u32,b:u32,reset:u32)->u32 decreases [a,b];{if b>0{return f(a+1,b-1,reset)+1;}if a>0{return f(a-1,reset,reset)+1;}return 0;}')
            with self.assertRaisesRegex(ValueError,'counterexample'):produce(source,self.compiler,root/'bad')

if __name__=='__main__':unittest.main()
