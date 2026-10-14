"""General word laws replay and conditions cannot be removed or invented."""
import copy
import gzip
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from ink_knowledge import Store, canonical, identity, semantic_entry
from producers.word_identities import specialize
from producers.author_word_identities import update_frozen_data


class WordIdentities(unittest.TestCase):
    def test_partial_authoring_preserves_existing_laws_and_hardlinked_snapshots(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'laws.json.gz'
            first=dict(name='first',law={'example':1})
            second=dict(name='second',law={'example':2})
            self.assertEqual(update_frozen_data(path,[first]),1)
            frozen=Path(tmp)/'frozen.json.gz';os.link(path,frozen)
            original=frozen.read_bytes()
            self.assertEqual(update_frozen_data(path,[second]),2)
            self.assertEqual(frozen.read_bytes(),original)
            self.assertEqual(json.loads(gzip.decompress(path.read_bytes())),[first,second])
            # A timeout/all-failure authoring batch has no checked new rows.
            self.assertEqual(update_frozen_data(path,[]),2)

    def test_all_laws_replay_and_renamed_sites_discover(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        rows=json.loads(gzip.decompress((root/'knowledge/producers/data/word-identities.json.gz').read_bytes()))
        self.assertEqual(len(rows),54)
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp); source=d/'source.ink'; core=d/'core.json'; subject=d/'subject.json'
            source.write_text('module independently_named;fn assemble(payload:u32,mask:u32)->u32{return (payload&mask)|(payload&word_not(mask));} fn bound(input:u64,mask:u64)->Bool{return (input&mask)<=mask;}')
            def run(*args):
                return subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=60)
            for command in [('emit-core',source,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
                result=run(*command); self.assertEqual(result.returncode,0,result.stderr)
            def check(objects, name):
                store=Store.publish(d/name,objects)
                view=d/(name+'.json');view.write_bytes(canonical(store.bundle([identity(o) for o in objects])))
                return run('knowledge-check',core,view)
            result=check([semantic_entry(r['law']) for r in rows],'valid')
            self.assertEqual(result.returncode,0,result.stderr)
            found=dict(specialize(json.loads(subject.read_bytes()),json.loads(core.read_bytes())))
            self.assertIn('word-identity/u32/complementary_partition',found)
            self.assertIn('word-identity/u64/mask_upper_bound',found)
            original=next(r['law'] for r in rows if r['name']=='u32/increment_with_room')
            bad=copy.deepcopy(original);bad['conditions']=[];bad['proof']['BitVector']['hypotheses']=[]
            self.assertNotEqual(check([semantic_entry(bad)],'missing-condition').returncode,0)
            bad=copy.deepcopy(original);bad['proof']['BitVector']['certificate']['steps']=[]
            self.assertNotEqual(check([semantic_entry(bad)],'missing-proof').returncode,0)
            self.assertEqual(specialize({'functions':{}},{}),[])

    def test_bounded_mask_laws_reuse_under_checked_premises(self):
        from ink_planner.semantic_search import match
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        rows=json.loads(gzip.decompress((root/'knowledge/producers/data/word-identities.json.gz').read_bytes()))
        with tempfile.TemporaryDirectory() as temporary:
            d=Path(temporary)
            for kind,width in [('u32',32),('u64',64)]:
                law=next(row['law'] for row in rows if row['name']==kind+'/bounded_low_mask')
                obj=semantic_entry(law);ident=identity(obj)
                store=Store.publish(d/kind,[obj]);view=store.bundle([ident])
                for mask in [0,1,255,(1<<width)-1,5]:
                    source=d/'source.ink';core=d/'core.json';subject=d/'subject.json';selection=d/'selection.json'
                    source.write_text('module renamed_'+kind+'; fn packet(payload:'+kind+')->'+kind+
                        '{return choose(payload<='+str(mask)+',word_and(payload,'+str(mask)+'),payload);}')
                    def run(*args):
                        return subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=60)
                    for command in [('emit-core',source,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
                        result=run(*command);self.assertEqual(result.returncode,0,result.stderr)
                    semantic=json.loads(subject.read_bytes());arguments={}
                    self.assertTrue(match(law['from'],semantic['functions']['packet'],law['params'],arguments))
                    package=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=semantic['input_core_sha256'],
                                 knowledge=view,applications=[dict(function='packet',path=[],law=ident,
                                                                  arguments=arguments,premises=['Normalize'])])
                    selection.write_bytes(canonical(package))
                    result=run('check-selection',core,selection)
                    if mask==5:
                        self.assertNotEqual(result.returncode,0,'noncontiguous mask must not satisfy premise')
                    else:
                        self.assertEqual(result.returncode,0,result.stderr)
                        for value in [0,1,2,255,256,(1<<width)-1]:
                            inputs=d/'inputs.json';inputs.write_text(json.dumps([value]))
                            result=run('run',core,'packet',inputs,'--core','--selection',selection)
                            self.assertEqual(result.returncode,0,result.stderr)
                            self.assertEqual(json.loads(result.stdout),value)
                forged=copy.deepcopy(law);forged['conditions']=[]
                forged['proof']['BitVector']['hypotheses']=[]
                bad=semantic_entry(forged);bad_store=Store.publish(d/(kind+'-forged'),[bad])
                invalid=d/'invalid.json';invalid.write_bytes(canonical(bad_store.bundle([identity(bad)])))
                self.assertNotEqual(run('knowledge-check',core,invalid).returncode,0)

    def test_new_snapshot_replays_new_law_in_fresh_checker_session(self):
        from ink_knowledge.proposal_views import ProposalViews
        from ink_planner.semantic_search import SelectionChecker, match
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink')).resolve()
        rows=json.loads(gzip.decompress((root/'knowledge/producers/data/word-identities.json.gz').read_bytes()))
        selected=[next(r['law'] for r in rows if r['name']==name)
                  for name in ('u32/complementary_partition','u64/mask_upper_bound')]
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);source=d/'source.ink';core=d/'core.json';subject=d/'subject.json'
            source.write_text('module growing_knowledge;fn assemble(payload:u32,mask:u32)->u32{return (payload&mask)|(payload&word_not(mask));} fn bound(input:u64,mask:u64)->Bool{return (input&mask)<=mask;}')
            for args in [('emit-core',source,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
                subprocess.run([str(compiler),*map(str,args)],check=True,capture_output=True)
            objects=[semantic_entry(l) for l in selected];ids=[identity(o) for o in objects]
            store=Store.publish(d/'base',[])
            views=ProposalViews(store,{ids[0]:objects[0]},d/'views')
            checker=SelectionChecker(compiler,core,views,d)
            functions=json.loads(subject.read_bytes())['functions'];apps=[]
            try:
                for i,name in enumerate(('assemble','bound')):
                    args={};self.assertTrue(match(selected[i]['from'],functions[name],selected[i]['params'],args))
                    apps.append(dict(function=name,path=[],law=ids[i],arguments=args,premises=[]))
                    if i:views.update({ids[i]:objects[i]})
                    self.assertTrue(checker.check(apps),checker.last_error)
                self.assertEqual(checker.session_attempts,2)
                self.assertEqual(checker.rejected_closures,0)
            finally:checker.close()


if __name__ == '__main__':
    unittest.main()
