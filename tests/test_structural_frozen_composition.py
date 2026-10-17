"""Versioned correspondence admits complete plans, not producer metadata."""
import json
import contextlib
import io
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
from producers import frozen_composition
from producers.fold_chunks import FoldChunks
from producers.action_replacement import MATH
from ink_knowledge import identity
from ink_knowledge.store import entry

ROOT=Path(__file__).resolve().parents[2]
INK=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()


class StructuralComposition(unittest.TestCase):
    def test_complete_plan_live_weights_events_rollback_and_mode_substitution(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder=Path(temporary)
            source=folder/'source.ink';source.write_text('''module structural;
enum Error { Failed, }
state Code:Table<u64,List<u32>>=Table.empty();
trainable state Weight:Table<u64,u32>=Table.empty();event changed:u32;
fn evaluate(code:List<u32>,w:u32,input:u32)->u32{
 return foldl(code,input,fn(op)=>fn(value)=>value*w+op);
}
learn change retune(w:u32,fail:Bool)->Result<Unit,Error> writes(Weight) emits(changed){
 Weight.put(0,w);emit changed(w);if fail{return Err(Error.Failed);}return Ok(());
}
adaptive query serve(input:u32)->u32 reads(Code,Weight){
 return evaluate(Code.get(0).unwrap_or([]),Weight.get(0).unwrap_or(1),input);
}''')
            def run(*args):
                result=subprocess.run([str(x) for x in args],capture_output=True,text=True,timeout=180)
                self.assertEqual(result.returncode,0,result.stderr[-4000:]);return result
            core=folder/'core.json';run(INK,'emit-core',source,'-o',core)
            data=json.loads(core.read_bytes());data['semantics']='ink-executable-core-v14'
            data['program']['frozen']={'Code':[[0,[0,1]*16]]};core.write_text(json.dumps(data))
            plan=folder/'plan.json'
            unused=entry('theorem',MATH,{'declaration':{'Theorem':dict(params=[],conditions=[],
                **{'from':{'U64':7},'to':{'U64':8}},proof={'Refl':{'U64':7}})}})
            unused_id=identity(unused);initialize=FoldChunks.__init__
            def with_unused_proposal(chunks,*args,**kwargs):
                initialize(chunks,*args,**kwargs)
                chunks.objects[unused_id]=unused;chunks.lemmas.add(unused_id)
            # Exercise multiple independently checked extension steps with a
            # smaller batch boundary; the kernel's 256-declaration cap stays.
            with patch.object(FoldChunks,'__init__',with_unused_proposal), patch.object(frozen_composition,'EXTENSION_BATCH_SIZE',2), patch('sys.argv',[
                    'frozen_composition',str(core),'--ink',str(INK),'--projection','structural-v2','-o',str(plan)]), contextlib.redirect_stdout(io.StringIO()):
                frozen_composition.main()
            packet=json.loads(plan.read_bytes())
            self.assertEqual(len(packet['steps']),3)
            self.assertNotEqual(packet['steps'][0]['package']['input_core_sha256'],packet['steps'][1]['package']['input_core_sha256'])
            self.assertEqual(packet['steps'][-1]['package']['action_replacement']['projection'],'structural-v2')
            self.assertNotIn(unused_id,packet['steps'][-1]['package']['knowledge']['objects'])
            run(INK,'check-plan',core,plan,'--core')
            run(INK,'build',core,'--core','--target','javascript','-o',folder/'before.mjs')
            run(INK,'compile',core,'--core','--plan',plan,'--target','javascript','-o',folder/'after.mjs')
            script=folder/'check.mjs';script.write_text('''import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
const [a,b]=await Promise.all(process.argv.slice(2).map(async p=>(await import(pathToFileURL(p))).createState()));
for(const [name,args] of [['serve',[7]],['retune',[3,false]],['serve',[7]],['retune',[9,true]],['serve',[7]],['retune',[0,false]],['serve',[7]]]){
 assert.deepEqual(a.invoke(name,args),b.invoke(name,args));
 assert.deepEqual(await a.checkpoint(),await b.checkpoint());
}''')
            run('node',script,folder/'before.mjs',folder/'after.mjs')
            packet['steps'][-1]['package']['action_replacement']['projection']='legacy'
            plan.write_text(json.dumps(packet))
            rejected=subprocess.run([INK,'check-plan',core,plan,'--core'],capture_output=True,text=True)
            self.assertNotEqual(rejected.returncode,0)
            packet['steps'][-1]['package']['action_replacement']['projection']='structural-v2'
            packet['steps'][1]['package']['input_core_sha256']=packet['input_core_sha256']
            plan.write_text(json.dumps(packet))
            rejected=subprocess.run([INK,'check-plan',core,plan,'--core'],capture_output=True,text=True)
            self.assertNotEqual(rejected.returncode,0)


if __name__=='__main__':unittest.main()
