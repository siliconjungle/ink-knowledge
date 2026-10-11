"""Exact authoring reproduction and mathematical controls for projected caches."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'producers'))
sys.path.insert(0,str(ROOT))
from representations import generate
from ink_knowledge import Store,identity


def wrong_field(request,directory):
    objects=json.loads(json.dumps(request['knowledge']['objects']))
    mappers=[e['payload']['declaration']['Function']for e in objects.values()
             if e['payload'].get('declaration',{}).get('Function',{}).get('params',[['']])[0][0]=='mapped_input']
    assert len(mappers)==1
    field=mappers[0]['body']['Match']['branches'][1]['body']['Construct']['arguments'][0]['Match']['branches'][0]
    assert field['body']=={'Var':field['bindings'][0]}
    field['body']={'Var':field['bindings'][1]}
    renamed,rebuilt,pending={},{},dict(objects)
    def rewrite(value):
        if isinstance(value,str):
            if value.startswith('call:'):return 'call:'+renamed.get(value[5:],value[5:])
            return renamed.get(value,value)
        if isinstance(value,dict):return {k:rewrite(v)for k,v in value.items()}
        if isinstance(value,list):return [rewrite(v)for v in value]
        return value
    while pending:
        ready=[k for k,e in pending.items()if not any(d in pending for d in e['dependencies'])]
        assert ready
        for old in ready:
            e=rewrite(pending.pop(old));e['dependencies']=sorted(set(e['dependencies']))
            e['interface']['operations']=sorted(set(e['interface']['operations']))
            new=identity(e);renamed[old]=new;rebuilt[new]=e
    rid=renamed[request['representation']]
    return dict(request,representation=rid,knowledge=Store.publish(directory,rebuilt.values()).bundle([rid]))


@unittest.skipUnless(os.environ.get('INK_COMPILER'),'requires explicit compiler')
class FieldCacheTests(unittest.TestCase):
    def test_frozen_mapped_point_proposal_reproduces(self):
        directory=ROOT/'research/field-caches';model=json.loads((directory/'model.json').read_text())
        with tempfile.TemporaryDirectory()as output:
            proposal=generate(model,output,cache_query='amount',preserve_cache=True,dynamic_delta=True)
        for label,request in zip(['direct','mapped'],proposal['requests']):
            self.assertEqual(request,json.loads((directory/(label+'.json')).read_text()))
        self.assertEqual(proposal['migration'],json.loads((directory/'migration.json').read_text()))

    def test_wrong_field_is_reauthenticated_then_mathematically_rejected(self):
        directory=ROOT/'research/field-caches'
        with tempfile.TemporaryDirectory()as output:
            request=wrong_field(json.loads((directory/'mapped.json').read_text()),Path(output)/'store')
            path=Path(output)/'forged.json';path.write_text(json.dumps(request))
            result=subprocess.run([os.environ['INK_COMPILER'],'check-representation',str(directory/'source.ink'),str(path)],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('definitional computation does not prove equality',result.stderr)

    def test_captured_state_is_not_treated_as_a_row_only_mapper(self):
        directory=ROOT/'research/field-caches';model=json.loads((directory/'model.json').read_text())
        reply=model['actions']['amount']['case']['normal']['Construct']['arguments'][0]
        body=reply['Match']['branches'][1]['body']['Construct']['arguments'][0]
        reply['Match']['branches'][1]['body']['Construct']['arguments'][0]={'Binary':dict(op='+',left=body,right={'Var':'additional_state'})}
        with tempfile.TemporaryDirectory()as output:
            with self.assertRaisesRegex(ValueError,'captures additional state'):
                generate(model,output,cache_query='amount',preserve_cache=True,dynamic_delta=True)

    def test_fixed_key_projection_laws_are_admitted_too(self):
        directory=ROOT/'research/field-caches'
        source=(directory/'source.ink').read_text()+'''
change replace_zero(amount:u64,label:u64)->Result<Unit,Error> writes(Rows){if Rows.contains(0){Rows.replace(0,Row{amount:amount,label:label});}else{return Err(Error.Failed);}return Ok(());}
change erase_zero()->Result<Unit,Error> writes(Rows){Rows.remove(0);return Ok(());}
'''
        with tempfile.TemporaryDirectory()as output:
            p=Path(output);(p/'source.ink').write_text(source)
            result=subprocess.run([os.environ['INK_COMPILER'],'emit-action-model',str(p/'source.ink'),'-o',str(p/'model.json')],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr)
            model=json.loads((p/'model.json').read_text())
            proposal=generate(model,p/'store',cache_query='amount',preserve_cache=True,delta_query=True)
            (p/'request.json').write_text(json.dumps(proposal['requests'][1]))
            result=subprocess.run([os.environ['INK_COMPILER'],'check-representation',str(p/'source.ink'),str(p/'request.json')],capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stderr)


if __name__=='__main__':unittest.main()
