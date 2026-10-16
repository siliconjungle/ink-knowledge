"""Range-guided representation proposals preserve modular boundaries and scope."""
import copy
import os
import json
import sys
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

from ink_knowledge import canonical
from producers.semantic_laws import value, var, word, op
from producers.word_facts import analyse_candidates, candidates
from tests.test_word_facts import evaluate


class RangeConversions(unittest.TestCase):
    def test_roundtrips_respect_branch_scope_wrapping_and_conversion_direction(self):
        u32, u64, boolean = value('U32'), value('U64'), value('Bool')
        x = var(u64, 'x'); y = var(u64, 'y'); small = var(u32, 'small')
        narrow = lambda a: op(u32, 'call:word_narrow_u64_to_u32', a)
        widen = lambda a: op(u64, 'call:word_widen_u32_to_u64', a)
        roundtrip = lambda a: widen(narrow(a))
        choose = lambda c,a,b: op(u64,'call:choose',c,a,b)
        bounded = op(boolean,'binary:<=',x,word('U64',(1<<32)-1))
        inc = op(u64,'binary:+',x,word('U64',1))
        sum_bound = op(boolean,'binary:<=',inc,word('U64',(1<<32)-1))
        relational = op(boolean,'binary:&&',op(boolean,'binary:<',x,y),
                        op(boolean,'binary:<=',y,word('U64',1<<32)))
        masked = op(u64,'call:word_and',x,word('U64',255))
        cases = [roundtrip(x),choose(bounded,roundtrip(x),x),
                 choose(bounded,x,roundtrip(x)),choose(relational,roundtrip(x),x),
                 choose(sum_bound,roundtrip(inc),inc),choose(sum_bound,roundtrip(x),x),
                 narrow(widen(small)),roundtrip(masked)]
        expected = [None,x,None,x,inc,None,small,masked]
        rng = random.Random(0x783812)
        inputs = [0,1,255,(1<<32)-1,1<<32,(1<<32)+1,(1<<64)-2,(1<<64)-1]
        inputs += [rng.getrandbits(64) for _ in range(64)]
        for source, replacement in zip(cases,expected):
            proposals = list(candidates(source))
            self.assertEqual(proposals,analyse_candidates(source)[1])
            if replacement is None:self.assertEqual(proposals,[])
            else:self.assertTrue(any(p==replacement for _,p in proposals))
            for n in inputs:
                for upper in [0,1,(1<<32)-1,1<<32,(1<<64)-1]:
                    env = dict(x=n,y=upper,small=n&((1<<32)-1))
                    for _,p in proposals:self.assertEqual(evaluate(source,env),evaluate(p,env))

    def test_normal_discovery_reuses_frozen_laws_with_renamed_inputs(self):
        from ink_knowledge import Store
        compiler = Path(os.environ['INK_COMPILER']).resolve()
        fixture = Path(__file__).parent/'fixtures/range-conversions/source.ink'
        with tempfile.TemporaryDirectory(prefix='ink-range-search-') as tmp:
            d=Path(tmp);source=d/'renamed.ink';core=d/'core.json';selection=d/'selected.json'
            source.write_text(fixture.read_text().replace('x:', 'data:').replace('(x)', '(data)').replace('x+', 'data+').replace('x<', 'data<').replace(',x', ',data').replace('upper','limit'))
            store=Store.publish(d/'knowledge',[])
            def run(*args):
                result=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=90)
                self.assertEqual(result.returncode,0,result.stderr[-3000:])
                return result
            run(compiler,'emit-core',source,'-o',core)
            run(sys.executable,'-m','ink_planner.semantic_search','--compiler',compiler,'--core',core,
                '--snapshot',store.data/'snapshot.json','--knowledge-root',store.root,
                '--budget','128','--rounds','4','--time-seconds','30','-o',selection)
            packet=json.loads(selection.read_bytes())
            self.assertTrue({'guarded','wrapped','relational'} <= {a['function'] for a in packet['applications']})
            run(compiler,'check-selection',core,selection)

    def test_whole_equations_replay_and_forged_scope_reject(self):
        from producers.conditional_facts import acquire
        compiler = Path(os.environ['INK_COMPILER']).resolve()
        source = Path(__file__).parent/'fixtures/range-conversions/source.ink'
        with tempfile.TemporaryDirectory(prefix='ink-range-conversion-') as tmp:
            d = Path(tmp)
            packet,receipt = acquire(source,compiler,d,seconds=15)
            self.assertEqual({a['function'] for a in packet['applications']},
                             {'guarded','relational','wrapped','small'})
            self.assertEqual(receipt['checked_laws'],4)
            for function in ['opposite','wrong_input','unchanged']:
                self.assertTrue(any(a['function']==function and a['status']=='no-candidate' for a in receipt['attempts']))
            # A source rehash and a different function name cannot transplant
            # facts from a guarded branch into the opposite arm.
            forged = copy.deepcopy(packet)
            forged['applications'] = [copy.deepcopy(next(a for a in packet['applications'] if a['function']=='guarded'))]
            forged['applications'][0]['function']='opposite'
            path=d/'forged.json';path.write_bytes(canonical(forged))
            result=subprocess.run([str(compiler),'check-selection',str(d/'core.json'),str(path)],capture_output=True,text=True,timeout=60)
            self.assertNotEqual(result.returncode,0)


if __name__ == '__main__':
    unittest.main()
