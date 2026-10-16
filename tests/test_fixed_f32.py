"""Integer-only proposals are checked against the independent fixed kernel."""
import copy
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

from ink_knowledge import Store, identity
from ink_knowledge.store import entry
from producers.action_replacement import MATH
from producers.fixed_f32 import evaluate

ROOT=Path(__file__).resolve().parents[2]
INK=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()


class FixedF32(unittest.TestCase):
    def test_integer_arithmetic_proposals_replay_in_the_kernel(self):
        boundaries=[0,0x80000000,1,0x80000001,0x7fffff,0x800000,0x3f000000,
            0x3f800000,0x3f800001,0xbf800001,0x7f7fffff,0xff7fffff,
            0x7f800000,0xff800000,0x7fa01234,0xffc05678]
        rng=random.Random(0x6a09e667)
        pairs=[(a,b)for a in boundaries for b in boundaries]+[(rng.getrandbits(32),rng.getrandbits(32))for _ in range(256)]
        cases=[(op,a,b)for a,b in pairs for op in ['+','-','*','div','==','!=','<','<=','>','>=']]
        cases += [(op,a,0)for a in boundaries+[rng.getrandbits(32)for _ in range(256)]
            for op in ['neg','sqrt','floor','ceil','trunc','round_ties_even','is_nan','is_finite']]
        cases += [(op,a,0)for a in [0,1,16777217,16777219,(1<<32)-1,1<<32,(1<<63)-1,1<<63,(1<<64)-1]+[rng.getrandbits(64)for _ in range(128)]
            for op in ['from_u32','from_u64','from_i32']]
        objects=[]
        for op,a,b in cases:
            left={'Binary':dict(op='f32:'+op,left={'U64':a},right={'U64':b})}
            right=evaluate('f32:'+op,a,b)
            theorem={'Theorem':dict(params=[],conditions=[],**{'from':left,'to':right},proof={'Convert':{'from':left,'to':right}})}
            objects.append(entry('theorem',MATH,{'declaration':theorem}))
        with tempfile.TemporaryDirectory() as directory:
            folder=Path(directory);source=folder/'source.ink';source.write_text('module fixed;fn identity(x:u32)->u32{return x;}')
            core=folder/'core.json';subprocess.run([INK,'emit-core',source,'-o',core],capture_output=True,check=True)
            store=Store.publish(folder/'store',objects)
            for offset in range(0,len(objects),2048):
                view=folder/'view.json';view.write_text(json.dumps(store.bundle([identity(o)for o in objects[offset:offset+2048]])))
                result=subprocess.run([INK,'knowledge-check',core,view],capture_output=True,text=True)
                self.assertEqual(result.returncode,0,result.stderr)
            # A fully rehashed adjacent result is still a false theorem.
            bad=copy.deepcopy(objects[0]);t=bad['payload']['declaration']['Theorem'];t['to']={'U64':1};t['proof']['Convert']['to']={'U64':1}
            forged=Store.publish(folder/'forged',[bad]);view.write_text(json.dumps(forged.bundle([identity(bad)])))
            result=subprocess.run([INK,'knowledge-check',core,view],capture_output=True,text=True)
            self.assertEqual(result.returncode,1);self.assertIn('does not prove equality',result.stderr)

    def test_unknown_operations_and_invalid_words_do_not_acquire_results(self):
        self.assertIsNone(evaluate('f32:unknown',1,2))
        for invalid in [True,-1,1<<64,'1']:
            with self.assertRaises(ValueError):evaluate('f32:+',invalid,0)


if __name__=='__main__':unittest.main()
