"""Untrusted universal slice proofs, instantiated by source element sorts.

The kernel supplies only fixed take/drop evaluation. These equalities are
database knowledge; no compiler matcher or timing fact grants applicability.
"""
from ink_knowledge import identity, semantic_entry
from producers.semantic_laws import value, arrow, var, op, law, term, word
from producers.beta_specialization15 import derive
from producers.definition_context28 import bind


def chain(middle,left,right):
    return {'Trans':dict(middle=middle,left=left,right=right)}


def named_laws(element='U32',output=None):
    output=element if output is None else output
    a,b=value(element),value(output)
    source_list,result_list=value({'List':element}),value({'List':output})
    xs,head,tail=var(source_list,'xs'),var(a,'head'),var(source_list,'tail')
    count=var(value('U32'),'count');previous=op(value('U32'),'binary:-',count,word('U32',1))
    condition=op(value('Bool'),'binary:==',count,word('U32',0))
    mapper=var(arrow(a,b),'mapper')
    apply=lambda f,x:op(f['sort']['Arrow'][1],'apply',f,x)
    mapping=lambda x:op(result_list,'method:map',x,mapper)
    slice_=lambda x,n,k:op(x['sort'],'method:'+n,x,k)
    rows=[]
    for operation in ('take','drop'):
        left=lambda x,k:slice_(mapping(x),operation,k)
        right=lambda x,k:mapping(slice_(x,operation,k))
        ih={'GeneralizedHypothesis':dict(index=0,arguments={'count':previous})}
        if operation=='take':
            cons=lambda t:term(result_list,{'Cons':[apply(mapper,head),t]})
            before,after=cons(left(tail,previous)),cons(right(tail,previous))
            step=chain(before,'Normalize',chain(after,{'Congruence':['Normalize',ih]},'Normalize'))
        else:
            before,after=left(tail,previous),right(tail,previous)
            step=chain(before,'Normalize',chain(after,ih,'Normalize'))
        proof={'GeneralizedInduction':dict(variable='xs',generalize=['count'],names=['head','tail'],base='Normalize',step={'Cases':dict(condition=condition,on_false=step,on_true='Normalize')})}
        rows.append((operation+'-before-map',law({'xs':source_list,'count':value('U32'),'mapper':mapper['sort']},left(xs,count),right(xs,count),proof)))
    if element==output:
        partition=lambda x,k:op(source_list,'method:concat',slice_(x,'take',k),slice_(x,'drop',k))
        before=term(source_list,{'Cons':[head,partition(tail,previous)]})
        after=term(source_list,{'Cons':[head,tail]})
        ih={'GeneralizedHypothesis':dict(index=0,arguments={'count':previous})}
        step=chain(before,'Normalize',chain(after,{'Congruence':['Normalize',ih]},'Normalize'))
        proof={'GeneralizedInduction':dict(variable='xs',generalize=['count'],names=['head','tail'],base='Normalize',step={'Cases':dict(condition=condition,on_false=step,on_true='Normalize')})}
        rows.append(('partition-reconstruction',law({'xs':source_list,'count':value('U32')},partition(xs,count),xs,proof)))
    return rows


def specialize(subject,core):
    """Type-driven instantiation plus generic typed matching and proof transport.

    Source bodies/names and target machines are never recognised as cases.
    Every nominal instantiation binds its full portable definition context.
    """
    pairs={}
    def visit(t):
        sort=t.get('sort') if isinstance(t,dict) else None
        if isinstance(sort,dict) and 'Arrow' in sort:
            a,b=sort['Arrow']
            if isinstance(a,dict) and set(a)=={'Value'} and isinstance(b,dict) and set(b)=={'Value'}:
                pairs[repr((a['Value'],b['Value']))]=(a['Value'],b['Value'])
        if isinstance(sort,dict) and isinstance(sort.get('Value'),dict) and 'List' in sort['Value']:
            element=sort['Value']['List'];pairs[repr((element,element))]=(element,element)
        if isinstance(t,dict):
            for x in t.values():visit(x)
        elif isinstance(t,list):
            for x in t:visit(x)
    visit(subject)
    if len(pairs)>64:raise ValueError('slice type-instantiation budget')
    generic=[]
    for a,b in pairs.values():
        for name,candidate in named_laws(a,b):
            candidate=bind(candidate,core,subject)
            generic.append((name+'-'+identity(semantic_entry(candidate)),candidate))
    # Generic endpoints and whole-source transports are proposals, never trusted
    # facts. The ordinary checker admits each selected dependency closure.
    rows=list(generic)
    for name,candidate in derive(subject,generic):
        try: rows.append((name,bind(candidate,core,subject)))
        except ValueError:
            # A supported outer body can call a function outside the admitted
            # semantic domain. It cannot carry this definition proof; retain
            # the other generic endpoints and independently supported sites.
            continue
    return rows


def main():
    """Publish only independently admitted reusable endpoints and discovery data."""
    import argparse,json,subprocess,tempfile
    from pathlib import Path
    from ink_knowledge import Store,canonical
    from ink_knowledge.store import entry
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--compiler',type=Path,required=True)
    p.add_argument('--knowledge-root',type=Path,required=True)
    p.add_argument('--report',type=Path,required=True)
    args=p.parse_args();compiler=args.compiler.resolve()
    sorts=['U32','U64','I32','F32','Bool','String','Int']
    objects=[];names={}
    for a in sorts:
        for b in sorts:
            for label,candidate in named_laws(a,b):
                obj=semantic_entry(candidate);objects.append(obj)
                names['list-slice/'+a+'/'+b+'/'+label]=identity(obj)
    with tempfile.TemporaryDirectory(prefix='ink-list-slice-publication-')as temporary:
        directory=Path(temporary);source=directory/'empty.ink';core=directory/'core.json'
        source.write_text('module proof_context; fn zero()->u32{return 0;}\n')
        subprocess.run([str(compiler),'emit-core',str(source),'-o',str(core)],check=True,capture_output=True)
        proposed=Store.publish(directory/'proposed',objects);view=directory/'view.json'
        view.write_bytes(canonical(proposed.bundle(sorted(identity(o)for o in objects)))+b'\n')
        result=subprocess.run([str(compiler),'knowledge-check',str(core),str(view)],check=True,capture_output=True,text=True)
        receipt=json.loads(result.stdout)
    root=args.knowledge_root.resolve();old=Store(root)
    # The producer is installed code selected by pinned database metadata, never
    # downloaded code or proof authority. Older snapshots do not activate it.
    discovery=entry('definition','ink-semantic-producers-v1',dict(module='producers.list_slice_laws'))
    from ink_knowledge.store import read
    aliases=read(root/'store/names.json');aliases.update(names)
    current=old.extend([*objects,discovery],aliases,leaf_size=64);current.refresh_index()
    args.report.parent.mkdir(parents=True,exist_ok=True)
    args.report.write_text(json.dumps(dict(schema=1,old_snapshot=old.snapshot_id,snapshot=current.snapshot_id,reusable_endpoints=len(objects),families=3,discovery=identity(discovery),compiler_sha256=__import__('hashlib').sha256(compiler.read_bytes()).hexdigest(),admission=receipt,scope='Universal typed slice equalities; source type/context instantiations require fresh kernel admission; no target profitability claim'),indent=2)+'\n')
    print(json.dumps(dict(snapshot=current.snapshot_id,reusable_endpoints=len(objects),families=3)))

if __name__=='__main__':main()
