"""Factored literal proofs remain ordinary source-bound checked theorems."""
import copy
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from ink_knowledge import Store, identity
from ink_knowledge.store import entry
from producers import frozen_specialization
from producers import closed_data_bridges
from producers.action_replacement import MATH, call, cons
from producers.closed_data_bridges import ClosedDataBridges

ROOT=Path(__file__).resolve().parents[2]
INK=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()

SOURCE='''module literals;
state Model:Table<u64,List<f32>>=Table.empty();
state Live:Table<u64,u64>=Table.empty();
query all()->List<f32> reads(Model){return Model.get(0).unwrap_or([]);}
query present()->Bool reads(Model){return Model.contains(0);}
query live()->u64 reads(Live){return Live.get(0).unwrap_or(0);}
change set(value:u64)->Unit writes(Live){Live.put(0,value);return ();}
'''

class ClosedDataProofs(unittest.TestCase):
    def fixture(self,temp,count):
        source,core=temp/'source.ink',temp/'core.json';source.write_text(SOURCE)
        subprocess.run([INK,'emit-core',source,'-o',core],check=True,capture_output=True)
        data=json.loads(core.read_bytes());data['semantics']='ink-executable-core-v14'
        words=[0,0x80000000,1,0x80000001,0x7fa01234,0xffc05678,0x7f800000,0xff800000,0x3e800001]
        data['program']['frozen']={'Model':[[0,[{'F32Bits':words[i%len(words)]}for i in range(count)]]]}
        core.write_text(json.dumps(data));return core

    def author(self,core,output):
        argv=['frozen_specialization',str(core),'--ink',str(INK),'-o',str(output)]
        with patch('sys.argv',argv),redirect_stdout(io.StringIO())as stdout:
            frozen_specialization.main()
        return json.loads(stdout.getvalue())

    def test_complete_exceptional_lists_use_checked_lemmas_and_preserve_every_checkpoint(self):
        with tempfile.TemporaryDirectory()as folder:
            temp=Path(folder)
            for count in [64,128,244,512]:
                core=self.fixture(temp,count);packet=temp/'selection.json'
                self.assertEqual(self.author(core,packet)['proof_strategy'],'compact')
                data=json.loads(packet.read_bytes())
                lemmas=[(i,e)for i,e in data['knowledge']['objects'].items()if e['kind']=='theorem']
                self.assertGreater(len(lemmas),0,count)
                for _,e in lemmas:
                    theorem=e['payload']['declaration']['Theorem']
                    self.assertEqual(theorem['params'],[]);self.assertEqual(theorem['conditions'],[])
                steps=[dict(call='all',args=[]),dict(call='present',args=[]),dict(call='set',args=[42]),dict(call='live',args=[]),dict(call='all',args=[])]
                for length in range(1,len(steps)+1):
                    script=temp/'script.json';script.write_text(json.dumps(steps[:length]));observed=[]
                    for selection in [None,packet]:
                        snapshot=temp/f'{selection is not None}.snapshot'
                        command=[INK,'execute',core,script,'--core','--portable','--snapshot-out',snapshot]
                        if selection:command+=['--selection',selection]
                        run=subprocess.run(command,check=True,capture_output=True)
                        observed.append((json.loads(run.stdout),snapshot.read_bytes()))
                    self.assertEqual(observed[0],observed[1],(count,length))
                # A different NaN payload cannot become equal merely because
                # both values classify as NaN or fail scalar IEEE equality.
                wrong=copy.deepcopy(data)
                action=next(a for a in wrong['action_replacement']['selected']['program']['actions']if a['name']=='all')
                values=action['body'][0]['Return']['Call'][1]
                exceptional=next(v for v in values if 'Call'in v and v['Call'][0]=='f32_from_bits')
                exceptional['Call'][1][0]['Num']^=1
                bad=temp/'wrong-payload.json';bad.write_text(json.dumps(wrong))
                self.assertNotEqual(subprocess.run([INK,'check-selection',core,bad],capture_output=True).returncode,0)

    def test_rehashed_invalid_theorem_is_checked_even_with_valid_membership(self):
        with tempfile.TemporaryDirectory()as folder:
            temp=Path(folder);core=self.fixture(temp,128);packet=temp/'selection.json';self.author(core,packet)
            data=json.loads(packet.read_bytes());objects=data['knowledge']['objects']
            # Add an invalid ordinary theorem with a fresh correct content hash
            # and authenticate it through a newly published database view.
            # Neither its role, hash nor membership can supply proof authority.
            obj=entry('theorem',MATH,{'declaration':{'Theorem':dict(params=[],conditions=[],
                **{'from':{'U64':0},'to':{'U64':1}},proof={'Refl':{'U64':0}})}})
            key=identity(obj);store=Store.publish(temp/'forged-database',[*objects.values(),obj])
            data['knowledge']=store.bundle([*data['knowledge']['roots'],key])
            bad=temp/'rehashed-proof.json';bad.write_text(json.dumps(data))
            rejected=subprocess.run([INK,'check-selection',core,bad],capture_output=True,text=True)
            self.assertNotEqual(rejected.returncode,0)
            self.assertIn('different statement',rejected.stderr)

    def test_wrong_nan_payload_rejects_after_rebuilding_the_source_bound_closure(self):
        with tempfile.TemporaryDirectory()as folder:
            temp=Path(folder);core=self.fixture(temp,128)
            selected=frozen_specialization.specialize(json.loads(core.read_bytes()))
            action=next(a for a in selected['program']['actions']if a['name']=='all')
            values=action['body'][0]['Return']['Call'][1]
            exceptional=next(v for v in values if 'Call'in v and v['Call'][0]=='f32_from_bits')
            exceptional['Call'][1][0]['Num']^=1
            candidate=temp/'wrong.core.json';candidate.write_text(json.dumps(selected))
            models=[]
            for name,source in [('before',core),('after',candidate)]:
                model=temp/(name+'.json')
                subprocess.run([INK,'emit-action-model',source,'--core','-o',model],check=True,capture_output=True)
                models.append(json.loads(model.read_bytes()))
            # Refresh every source-derived action/definition and membership;
            # a source-identity mismatch is not the rejection being tested.
            packet=frozen_specialization.produce(*models,selected,temp/'wrong-database',compact=True)
            file=temp/'wrong-selection.json';file.write_text(json.dumps(packet))
            rejected=subprocess.run([INK,'check-selection',core,file],capture_output=True,text=True)
            self.assertNotEqual(rejected.returncode,0)
            self.assertIn('action all:',rejected.stderr)
            self.assertNotIn('source-bound transition definition',rejected.stderr)

    def test_optional_discovery_budget_keeps_the_prior_checked_tactic(self):
        with tempfile.TemporaryDirectory()as folder:
            temp=Path(folder);core=self.fixture(temp,64);packet=temp/'selection.json'
            with patch.object(ClosedDataBridges,'MAX_WORK',0):
                self.author(core,packet)
            data=json.loads(packet.read_bytes())
            self.assertFalse(any(e['kind']=='theorem'for e in data['knowledge']['objects'].values()))
            subprocess.run([INK,'check-selection',core,packet],check=True,capture_output=True)
            original_entry=closed_data_bridges.entry;calls=0
            def exhaust_after_one_lemma(*args,**kwargs):
                nonlocal calls
                calls+=1
                if calls==2:raise ValueError('knowledge object byte limit')
                return original_entry(*args,**kwargs)
            with patch.object(closed_data_bridges,'entry',side_effect=exhaust_after_one_lemma):
                self.author(core,packet)
            self.assertEqual(calls,2)
            data=json.loads(packet.read_bytes())
            self.assertFalse(any(e['kind']=='theorem'for e in data['knowledge']['objects'].values()))
            subprocess.run([INK,'check-selection',core,packet],check=True,capture_output=True)

    def test_dynamic_binders_cycles_and_distinct_literal_values_are_not_bridge_candidates(self):
        # These are only opportunity inputs; actual admission still requires
        # typed definitions and proof replay. No malformed source is admitted.
        def function(body):
            return entry('definition',MATH,{'declaration':{'Function':dict(params=[],result={'Data':'a'*64},body=body,recursive=None)}})
        a,b='1'*64,'2'*64
        for objects in [
            {a:function({'Var':'live'}),b:function({'Var':'live'})},
            {a:function(call(b,[])),b:function(call(a,[]))},
            {a:function(cons('a'*64,0,[{'U64':0}])),b:function(cons('a'*64,0,[{'U64':1}]))},
        ]:
            result=ClosedDataBridges(objects)
            self.assertEqual(result.aliases,{})
            self.assertEqual(result.lemmas,set())
            self.assertEqual(result.objects,objects)

if __name__=='__main__':unittest.main()
