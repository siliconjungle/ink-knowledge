"""Whole-function composition retains binders, branches and every premise."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.proposal_views import ProposalViews
from ink_planner.semantic_search import positions,replace,substitute
from producers.semantic_laws import law,value,var,word,op,bound
from producers.selection_composition import compose
from producers.guarded_choices import guarded_rows

ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()

class SelectionComposition(unittest.TestCase):
    def compiler(self,*args,success=True):
        r=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True,timeout=120)
        self.assertEqual(r.returncode==0,success,r.stdout[-1000:]+r.stderr[-3000:]);return r
    def source(self,d,text):
        (d/'source.ink').write_text(text);self.compiler('emit-core',d/'source.ink','-o',d/'core.json')
        self.compiler('emit-semantic',d/'core.json','--core','-o',d/'subject.json')
        return json.loads((d/'core.json').read_text()),json.loads((d/'subject.json').read_text()),Store.publish(d/'knowledge',[])
    def packet(self,subject,store,objects,applications,d):
        return dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],
            applications=applications,knowledge=ProposalViews(store,objects,d).bundle(sorted(objects)))
    def check(self,d,packet,name,success=True):
        p=d/(name+'.json');p.write_bytes(canonical(packet));self.compiler('check-selection',d/'core.json',p,success=success)
        if success:self.compiler('build',d/'core.json','--core','--selection',p,'--target','javascript','-o',d/(name+'.mjs'))
    def node(self,d,text):
        (d/'test.mjs').write_text(text);r=subprocess.run(['node',str(d/'test.mjs')],capture_output=True,text=True,timeout=60)
        self.assertEqual(r.returncode,0,r.stderr)

    def test_repeated_local_steps_under_two_lambdas_preserve_premise_scope(self):
        with tempfile.TemporaryDirectory()as temporary:
            d=Path(temporary);core,subject,store=self.source(d,'module nested; fn run(composed_argument:List<u32>,ys:List<u32>)->List<List<u32>>{return composed_argument.map(fn(x)=>ys.map(fn(y)=>(x+0)+(y+0)));}')
            u=value('U32');x,z=var(u,'x'),var(u,'z')
            reflexive=semantic_entry(law({'z':u},z,z,'Normalize'));rid=identity(reflexive)
            rule=semantic_entry(law({'x':u,'z':u},op(u,'binary:+',x,word('U32',0)),x,'Normalize',conditions=[{'from':z,'to':z}]))
            ident=identity(rule);body=subject['functions']['run'];apps=[]
            for _ in range(2):
                path,t=next((p,t)for p,t in positions(body)if isinstance(t['node'],dict)and t['node'].get('Op',[None])[0]=='binary:+'and t['node']['Op'][1][1]==word('U32',0))
                xarg=t['node']['Op'][1][0];self.assertIn(xarg['node']['Bound'],[0,1])
                other=bound(u,1-xarg['node']['Bound'])
                args={'x':xarg,'z':other}
                apps.append(dict(function='run',path=list(path),law=ident,arguments=args,
                    premises=[{'Use':dict(law=rid,arguments={'z':other},premises=[])}]))
                body=replace(body,path,substitute(rule['payload']['to'],args))
            packet=self.packet(subject,store,{rid:reflexive,ident:rule},apps,d/'original')
            self.check(d,packet,'local')
            combined=compose(packet,subject,core,store,d/'composed');self.assertEqual(len(combined['applications']),1)
            self.assertEqual(combined['applications'][0]['path'],[]);self.check(d,combined,'whole')
            # Joint guard authoring can now guard the complete transformed body.
            row=dict(status='proposal',label='composed',step=dict(kind='rewrite',package=combined))
            guarded=list(guarded_rows(row,store,d/'guarded',8,joint=True));self.assertEqual(len(guarded),1)
            self.check(d,guarded[0]['steps'][-1]['package'],'guarded')
            local_row=dict(status='proposal',label='local',step=dict(kind='rewrite',package=packet))
            integrated=list(guarded_rows(local_row,store,d/'integrated-guard',8,joint=True,subject=subject,core=core))
            self.assertEqual(len(integrated),1);self.check(d,integrated[0]['steps'][-1]['package'],'integrated-guard')
            self.node(d,"""import assert from 'node:assert/strict';import * as a from './local.mjs';import * as b from './whole.mjs';import * as c from './guarded.mjs';
for(const n of [0,1,7,8,9])for(const q of [0,1,7,8,9]){
 const xs=Array.from({length:n},(_,i)=>[0,1,4294967295][i%3]),ys=Array.from({length:q},(_,i)=>[4294967295,7][i%2]);
 const before=structuredClone([xs,ys]),expected=xs.map(x=>ys.map(y=>(x+y)>>>0));
 for(const m of [a,b,c])assert.deepEqual(m.call('run',[xs,ys]),expected);assert.deepEqual([xs,ys],before);
} """)
            bad=copy.deepcopy(combined);objects=bad['knowledge']['objects'];old=objects[bad['applications'][0]['law']]
            authored=dict(schema=1,semantics=old['semantics'],dependencies=old['dependencies'],**copy.deepcopy(old['payload']))
            def erase(v):
                if isinstance(v,dict):
                    if 'Use'in v and v['Use']['law']==ident:v['Use']['premises']=[];return True
                    return any(erase(x)for x in v.values())
                return isinstance(v,list)and any(erase(x)for x in v)
            self.assertTrue(erase(authored['proof']));obj=semantic_entry(authored);new=identity(obj)
            bad['applications'][0]['law']=new;bad['knowledge']=ProposalViews(store,{**objects,new:obj},d/'forged').bundle([new])
            self.check(d,bad,'missing-premise',success=False)

    def test_bitvector_premise_survives_callback_alpha_renaming(self):
        from producers.bitvector_proofs import certificate
        with tempfile.TemporaryDirectory()as temporary:
            d=Path(temporary);core,subject,store=self.source(d,'module word_premise; fn run(xs:List<u32>,a:u32)->List<u32>{return xs.map(fn(x)=>word_and(x,31)+a*0);}')
            u=value('U32');boolean=value('Bool');x,a=var(u,'x'),var(u,'a')
            masked=op(u,'call:word_and',x,word('U32',31));condition=op(boolean,'binary:<=',masked,op(u,'call:word_or',a,word('U32',31)))
            true=dict(sort=boolean,node={'Bool':True})
            rule=semantic_entry(law({'x':u,'a':u},op(u,'binary:+',masked,op(u,'binary:*',a,word('U32',0))),masked,'Normalize',conditions=[{'from':condition,'to':true}]))
            ident=identity(rule);body=subject['functions']['run']
            path,target=next((p,t)for p,t in positions(body)if isinstance(t['node'],dict)and t['node'].get('Op',[None])[0]=='binary:+')
            opened_condition=substitute(condition,{'x':var(u,'__ink_scope_0'),'a':a})
            goal=dict(params={'__ink_scope_0':u,'a':u},conditions=[],**{'from':opened_condition,'to':true})
            (d/'goal.json').write_bytes(canonical(goal));self.compiler('semantic-bitvector-obligation',d/'core.json',d/'goal.json','--core','-o',d/'cnf.json')
            proof=certificate(json.loads((d/'cnf.json').read_text()),seconds=5,conflicts=20000,total_seconds=5)
            apps=[dict(function='run',path=list(path),law=ident,arguments={'x':bound(u,0),'a':a},
                premises=[{'BitVector':dict(hypotheses=[],certificate=proof)}])]
            packet=self.packet(subject,store,{ident:rule},apps,d/'local-proof');self.check(d,packet,'local')
            combined=compose(packet,subject,core,store,d/'whole-proof');self.check(d,combined,'whole')
            self.node(d,"""import assert from 'node:assert/strict';import * as m from './whole.mjs';
for(const xs of [[],[0,1,31,32,4294967295]])for(const a of [0,1,4294967295])assert.deepEqual(m.call('run',[xs,a]),xs.map(x=>x&31)); """)

    def test_branch_and_lazy_boolean_facts_remain_scoped(self):
        with tempfile.TemporaryDirectory()as temporary:
            d=Path(temporary);core,subject,store=self.source(d,'module branch; fn run(xs:List<Bool>,flag:Bool)->List<Bool>{return xs.map(fn(x)=>choose(flag,x && flag,x || flag));}')
            boolean=value('Bool');p=var(boolean,'p');objects={};rules={}
            for flag in [True,False]:
                target=dict(sort=boolean,node={'Bool':flag})
                obj=semantic_entry(law({'p':boolean},p,target,{'Hypothesis':0},conditions=[{'from':p,'to':target}]))
                ident=identity(obj);objects[ident]=obj;rules[flag]=(ident,obj)
            body=subject['functions']['run'];apps=[]
            for flag,operator in [(True,'binary:&&'),(False,'binary:||')]:
                path,t=next((p,t)for p,t in positions(body)if isinstance(t['node'],dict)and t['node'].get('Op',[None])[0]==operator)
                ident,obj=rules[flag];path=path+(1,);args={'p':var(boolean,'flag')}
                apps.append(dict(function='run',path=list(path),law=ident,arguments=args,premises=[{'Hypothesis':0}]))
                body=replace(body,path,substitute(obj['payload']['to'],args))
            packet=self.packet(subject,store,objects,apps,d/'local');self.check(d,packet,'local')
            combined=compose(packet,subject,core,store,d/'whole');self.check(d,combined,'whole')
            self.node(d,"""import assert from 'node:assert/strict';import * as a from './local.mjs';import * as b from './whole.mjs';
for(const xs of [[],[false],[true],[true,false,true]])for(const flag of [true,false]){
 const expected=xs.map(x=>flag?(x&&flag):(x||flag));for(const m of [a,b])assert.deepEqual(m.call('run',[xs,flag]),expected);
} """)
            mismatch=dict(subject,input_core_sha256='0'*64)
            with self.assertRaisesRegex(ValueError,'source mismatch'):compose(packet,mismatch,core,store,d/'mismatch')
            oversized=dict(packet,applications=packet['applications']*65)
            with self.assertRaisesRegex(ValueError,'application budget'):compose(oversized,subject,core,store,d/'oversized')
            bad=copy.deepcopy(packet);bad['applications'][0]['path']=[999]
            with self.assertRaisesRegex(ValueError,'path'):compose(bad,subject,core,store,d/'bad-path')

if __name__=='__main__':unittest.main()
