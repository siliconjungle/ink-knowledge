"""Publish checked source contract algebra and untrusted instantiation templates.

Source proofs are checked before publication. Templates preserve those ordinary
proofs; every concrete generated law is checked again at use. Template membership
or a source declaration's name gives no theorem authority.
"""
import argparse,copy,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import Store,entry,identity,canonical
from producers.bag_laws import examples as bag_examples

def sorting_contracts(compiler,store):
    """Whole multiset observations proved from ordinary multiplicity laws."""
    from producers.semantic_observations import proposals
    from ink_knowledge import semantic_entry
    objects={};names={}
    with tempfile.TemporaryDirectory(prefix='ink-sorting-contracts-')as directory:
        directory=Path(directory);source=directory/'source.ink';goals=directory/'goals.json'
        source.write_text('module sorting_contracts;\n'+''.join(
            f'spec fn bag_{t}(xs:List<{t}>)->List<{t}> ensures multiset(result)==multiset(xs);\nimplementation ordered_{t} for bag_{t} {{return xs.sort();}}\n'
            for t in ('u32','u64','i32')))
        subprocess.run([compiler,'emit-contract-obligations',str(source),'-o',str(goals)],capture_output=True,text=True,check=True)
        exported=json.loads(goals.read_text())
        for goal in exported['pure']:
            if not goal['name'].startswith('bag_'):continue
            for proof,bundle in proposals(goal,store,exported['definition_context']):
                trial=directory/'trial.json';trial.write_bytes(canonical(dict(proof=proof,knowledge=bundle)))
                checked=subprocess.run([compiler,'check-contract-proof',str(source),goal['name'],str(trial)],capture_output=True,text=True)
                if checked.returncode==0:
                    law=dict(schema=1,semantics='ink-conditional-laws-v1',params=goal['params'],conditions=goal['conditions'],**goal['goal'],proof=proof,dependencies=bundle['roots'])
                    obj=semantic_entry(law);ident=identity(obj);objects.update(bundle['objects']);objects[ident]=obj
                    names['bags/sort-contract-'+goal['name'].split(':')[0][4:]]=ident;break
            else:raise ValueError('unclosed sorting observation '+goal['name']+': '+checked.stderr)
    return objects,names

def templates(objects):
    made={};mapping={}
    def convert(ident,active=()):
        if ident in mapping:return mapping[ident]
        if ident in active or len(active)>16:raise ValueError('algebra template dependency cycle')
        law=dict(copy.deepcopy(objects[ident]['payload']),schema=1,semantics=objects[ident]['semantics'],dependencies=objects[ident]['dependencies']);names=law.get('types',[])
        if not names or law.get('assumptions'):return None
        dependencies={}
        for number,dependency in enumerate(law['dependencies']):
            target=convert(dependency,(*active,ident))
            if target is None:return None
            dependencies['$dependency_'+str(number)]=target
        labels=dict(zip(law['dependencies'],dependencies))
        def transform(value):
            if isinstance(value,dict):
                if set(value)=={'Named'}and value['Named']in names:return {'Named':'$'+value['Named']}
                if 'Use'in value:
                    use=copy.deepcopy(value['Use']);use['law']=labels.get(use['law'],use['law']);use.pop('types',None);use.pop('assumptions',None)
                    return {'Use':transform(use)}
                return {k:transform(v)for k,v in value.items()}
            if isinstance(value,list):return [transform(v)for v in value]
            return value
        law=transform(law);law['semantics']='ink-conditional-laws-v1';law.pop('types',None);law.pop('assumptions',None);law['dependencies']=[]
        obj=entry('definition','ink-semantic-law-template-v1',dict(type_parameters=names,law=law,dependencies=dependencies),dependencies.values())
        target=identity(obj);made[target]=obj;mapping[ident]=target;return target
    for ident in objects:convert(ident)
    return made,mapping

def publish(compiler,root):
    root=Path(root);library=Path(__file__).resolve().parents[1]/'libraries';compiler=str(Path(compiler).resolve())
    with tempfile.TemporaryDirectory(prefix='ink-contract-algebra-')as temporary:
        bundle=Path(temporary)/'laws.json'
        run=subprocess.run([compiler,'emit-laws',str(library/'contract-algebra.ink'),'--proofs',str(library/'contract-algebra.proofs.json'),'-o',str(bundle)],capture_output=True,text=True,timeout=120)
        if run.returncode:raise ValueError(run.stderr)
        receipt=json.loads(run.stdout);view=json.loads(bundle.read_text())
    objects=dict(view['objects']);names={'contract-algebra/'+n:i for n,i in receipt['names'].items()}
    from ink_knowledge import semantic_entry
    for name,law in bag_examples().items():
        obj=semantic_entry(law);ident=identity(obj);objects[ident]=obj;names[name]=ident
    # Empty application packages still admit their full enabled proof closure.
    # Replay the externally constructed multiplicity/observer laws before adding
    # them to the publication, using the selected compiler's actual checker.
    with tempfile.TemporaryDirectory(prefix='ink-bag-replay-')as temporary:
        temporary=Path(temporary);source=temporary/'stub.ink';core=temporary/'stub.core.json'
        source.write_text('module bag_replay;fn identity(x:u32)->u32{return x;}\n')
        run=subprocess.run([compiler,'emit-core',str(source),'-o',str(core)],capture_output=True,text=True,check=True)
        source_id=json.loads(run.stdout)['core_sha256']
        from ink_knowledge.implementation_candidates import identity_selection
        bag_objects={i:o for i,o in objects.items()if i in {names[n]for n in bag_examples()}}
        bag_store=Store.publish(temporary/'database',bag_objects.values());packet=identity_selection(source_id);packet['knowledge']=bag_store.bundle(sorted(bag_objects))
        selected=temporary/'selection.json';selected.write_bytes(canonical(packet))
        subprocess.run([compiler,'check-selection',str(core),str(selected)],capture_output=True,text=True,check=True)
    generated,mapping=templates(objects);objects.update(generated)
    for name,ident in list(names.items()):
        if ident in mapping:names['templates/'+name]=mapping[ident]
    previous=Store(root)if(root/'store/snapshot.json').exists()else None
    store=previous.extend(objects.values(),names)if previous else Store.publish(root,objects.values(),names)
    store.refresh_index()
    composed,composed_names=sorting_contracts(compiler,store);objects.update(composed);names.update(composed_names)
    store=store.extend(composed.values(),composed_names)
    store.refresh_index()
    roots=sorted(i for i,o in objects.items()if o['kind']=='rewrite')
    (root/'store/contract-algebra-view.json').write_bytes(canonical(store.bundle(roots))+b'\n')
    report=dict(schema=1,snapshot=store.snapshot_id,source_laws=len(view['roots']),multiplicity_laws=len(bag_examples()),observation_laws=len(composed_names),templates=len(generated),objects=len(objects),names=names)
    (root/'store/contract-algebra-publication.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--compiler',required=True);p.add_argument('--output-store',required=True);a=p.parse_args();print(json.dumps(publish(a.compiler,a.output_store)))
if __name__=='__main__':main()
