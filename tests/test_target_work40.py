"""Diagnostic instrumentation preserves actual values; counts only literal sites."""
import json,shutil,subprocess,sys,tempfile,unittest
from pathlib import Path
K=Path(__file__).resolve().parents[1];B=K.parent;sys.path.insert(0,str(K))
PARSER=B/'reports/web-stack-engine-40-2026-10-11/cost/tools/node_modules/acorn/dist/acorn.mjs'
from producers.target_work40_c import instrument

@unittest.skipUnless(shutil.which('node')and PARSER.exists(),'optional Acorn diagnostic parser unavailable')
class JSWorkTests(unittest.TestCase):
    def run_fixture(self,source,expected,args):
        with tempfile.TemporaryDirectory()as d:
            r=Path(d);original=r/'original.mjs';original.write_text(source);out=r/'instrumented.mjs';receipt=r/'instrumentation.json';fixtures=r/'fixtures.json';fixtures.write_text(json.dumps([dict(id='f',entry='f',args=args,expected=expected,boundary='owned')]))
            subprocess.run(['node',str(K/'producers/target_work40_js.mjs'),str(original),str(out),str(receipt),str(PARSER)],check=True,capture_output=True)
            result=subprocess.run(['node',str(K/'producers/target_work40_replay.mjs'),str(original),str(out),str(receipt),str(fixtures),str(r/'trace.json')],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr);return json.loads((r/'trace.json').read_text())['rows'][0]
    def test_branches_break_continue_shadowed_helpers_and_shared_carrier(self):
        source='''function helper(xs){const a=[];for(let i=0;i<xs.length;i++){if(i===1)continue;if(i===3)break;a.push(xs[i]);}return a;}export function call(name,args){const a=helper(args[0]);for(let i=0;i<a.length;i++){let a=i;a+=2;}return a;}'''
        row=self.run_fixture(source,[7,9],[[7,8,9,10,11]])
        self.assertEqual(row['components']['loop_iterations'],6);self.assertEqual(row['components']['allocation_events'],1);self.assertTrue(all(row['known'].values()))
    def test_typed_copy_byte_extents_and_complete_outputs(self):
        source='''export function call(name,args){const a=new Uint32Array(args[0]);const b=new Uint32Array(a.length);b.set(a);return b.slice(1);}'''
        row=self.run_fixture(source,[8,9],[[7,8,9]])
        self.assertEqual(row['components']['allocation_events'],3);self.assertEqual(row['components']['copy_bytes'],20);self.assertFalse(row['known']['copy_bytes'])
    def test_custom_methods_are_opaque_native_callbacks_counted(self):
        source='''export function call(name,args){let hits=0;const a={get slice(){hits++;return function(x){return [hits+x];}}};const b=a.slice(2);return b;}'''
        row=self.run_fixture(source,[3],[]);self.assertFalse(row['known']['allocation_events']);self.assertFalse(row['known']['loop_iterations'])
        source='''export function call(name,args){return args[0].map(x=>x+1);}'''
        row=self.run_fixture(source,[8,9],[[7,8]]);self.assertTrue(row['known']['loop_iterations']);self.assertEqual(row['components']['loop_iterations'],2)
    def test_nested_receiver_edits_fail_closed(self):
        with tempfile.TemporaryDirectory()as d:
            r=Path(d);(r/'s.mjs').write_text('export function call(){return new Uint32Array(3).slice(1);}')
            result=subprocess.run(['node',str(K/'producers/target_work40_js.mjs'),str(r/'s.mjs'),str(r/'out.mjs'),str(r/'receipt.json'),str(PARSER)],capture_output=True)
            self.assertNotEqual(result.returncode,0);self.assertFalse((r/'receipt.json').exists())

@unittest.skipUnless(shutil.which('clang'),'optional Clang AST unavailable')
class CWorkTests(unittest.TestCase):
    def test_literal_nonblock_loop_copy_and_allocator_sites(self):
        with tempfile.TemporaryDirectory()as d:
            r=Path(d);p=r/'s.c';p.write_text('''#include <stddef.h>\nvoid *ink_alloc(size_t n,size_t w){return 0;}void ink_copy(void*a,const void*b,size_t bytes){for(size_t i=0;i<bytes;i++)((char*)a)[i]=((char*)b)[i];}unsigned f(unsigned n){unsigned a=0;for(unsigned i=0;i<n;i++)if(i%2)a++;return a;}''')
            data=instrument(p,r/'out.c',r/'receipt.json');self.assertEqual(sum(x['kind']=='loop_iterations'for x in data['sites']),2);self.assertEqual(sum(x['kind']=='allocation_events'for x in data['sites']),1);self.assertEqual(sum(x['kind']=='explicit_copy_bytes'for x in data['sites']),1)
    def test_missing_primitive_scope_is_unknown(self):
        with tempfile.TemporaryDirectory()as d:
            r=Path(d);p=r/'s.c';p.write_text('unsigned f(unsigned n){for(unsigned i=0;i<n;i++)n+=0;return n;}')
            data=instrument(p,r/'out.c',r/'receipt.json');self.assertEqual({x for u in data['unknown']for x in u['components']},{'allocation_events','copy_bytes'})
if __name__=='__main__':unittest.main()
