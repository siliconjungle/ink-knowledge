"""Conditional higher-order adapters preserve ordinary proof obligations."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from ink_knowledge import Store, canonical, identity, entry
from ink_knowledge.proposal_views import ProposalViews
from ink_knowledge.law_templates import SEMANTICS, generate
from producers.semantic_laws import value, arrow, var, bound, lam, op, law, term


class ConditionalAdapters(unittest.TestCase):
    def test_conditions_replay_at_renamed_callback_sites(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        a=value({'Named':'$A'});seq=value({'List':{'Named':'$A'}});boolean=value('Bool')
        xs=var(seq,'xs');f=var(arrow(a,a),'f');flag=var(boolean,'flag')
        mapped=op(seq,'method:map',xs,lam(a,op(a,'apply',f,bound(a,0))))
        source=op(seq,'call:choose',flag,mapped,xs)
        candidate=law(dict(xs=seq,f=f['sort'],flag=boolean),source,mapped,'Normalize',
                      conditions=[dict(**{'from':flag,'to':term(boolean,{'Bool':True})})])
        template=entry('definition',SEMANTICS,dict(type_parameters=['A'],law=candidate,dependencies={}))
        with tempfile.TemporaryDirectory()as temporary:
            d=Path(temporary);store=Store.publish(d/'store',[template]);store.refresh_index()
            for kind,body,inputs,expected,capture,extras in [
                ('u32','x+1',[0,255,4294967295],[1,256,0],'',[]),
                ('Bool','!x',[True,False],[False,True],'',[]),
                ('u64','x+offset',[0,255,18446744073709551615],[3,258,2],',offset:u64',[3])]:
                for name,guard,params in [('known','true',''),('unknown','enabled',',enabled:Bool'),('off','false','')]:
                    with self.subTest(kind=kind,case=name):
                        source_path=d/'source.ink';core=d/'core.json';subject=d/'subject.json'
                        source_path.write_text('module conditional_adapter;fn run(values:List<'+kind+'>'+capture+params+
                            ')->List<'+kind+'>{return choose('+guard+',values.map(fn(x)=>'+body+'),values);}')
                        def call(*args):
                            return subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=60)
                        for command in [('emit-core',source_path,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
                            result=call(*command);self.assertEqual(result.returncode,0,result.stderr)
                        sem=json.loads(subject.read_bytes());objects,_=generate(store,sem,json.loads(core.read_bytes()))
                        adapters=[(i,o)for i,o in objects.items()if o['payload']['from']==sem['functions']['run']]
                        self.assertEqual(len(adapters),1)
                        ident,adapter=adapters[0]
                        self.assertEqual(len(adapter['payload']['conditions']),1)
                        view=ProposalViews(store,objects,d/('views-'+kind+'-'+name)).bundle([ident])
                        view_path=d/'view.json';view_path.write_bytes(canonical(view))
                        result=call('knowledge-check',core,view_path);self.assertEqual(result.returncode,0,result.stderr)
                        arguments={n:var(s,n)for n,s in adapter['payload']['params'].items()}
                        package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=sem['input_core_sha256'],knowledge=view,
                            applications=[dict(function='run',path=[],law=ident,arguments=arguments,premises=['Normalize'])])
                        selection=d/'selection.json';selection.write_bytes(canonical(package))
                        result=call('check-selection',core,selection)
                        self.assertEqual(result.returncode==0,name=='known',result.stderr)
                        if name=='known':
                            values=d/'inputs.json';values.write_text(json.dumps([inputs,*extras]))
                            result=call('run',core,'run',values,'--core','--selection',selection)
                            self.assertEqual(result.returncode,0,result.stderr)
                            self.assertEqual(json.loads(result.stdout),expected)
                        for mode in ['remove-condition','change-result']:
                            forged=copy.deepcopy(adapter)
                            if mode=='remove-condition':forged['payload']['conditions']=[]
                            else:forged['payload']['to']=var(value({'List':{'u32':'U32','u64':'U64','Bool':'Bool'}[kind]}),'values')
                            bad=Store.publish(d/('bad-'+kind+'-'+name+'-'+mode),
                                [forged if i==ident else o for i,o in objects.items()])
                            view_path.write_bytes(canonical(bad.bundle([identity(forged)])))
                            result=call('knowledge-check',core,view_path)
                            self.assertNotEqual(result.returncode,0)
