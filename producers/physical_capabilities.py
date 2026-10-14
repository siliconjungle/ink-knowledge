"""Untrusted source capabilities: RUP bounds, inductive codecs and field equality.

All proposals are replayed by Ink. This producer owns search and profitability;
the compiler exports obligations and admits proofs, never imports this module.
"""
import argparse, json, subprocess, tempfile
from pathlib import Path
from ink_knowledge import Store, identity, canonical
from ink_knowledge.store import entry
from producers.action_replacement import var, call, cons, convert, trans
from producers.bitvector_proofs import certificate
from producers.workspace import compiler_path
MATH='first-order-inductive-equality-v1'
READ='ink-source-read-capability-v1'
MAP='ink-source-column-map-v1'

def invoke(compiler,*args):
    result=subprocess.run([str(compiler),*map(str,args)],capture_output=True,text=True,timeout=120)
    if result.returncode:raise ValueError(result.stderr.strip())
    return result.stdout

def write(path,value):path.write_bytes(canonical(value)+b'\n');return path

def bit_proof(compiler,directory,goal):
    path=write(directory/'goal.json',goal);out=directory/'cnf.json'
    invoke(compiler,'bitvector-obligation',path,'-o',out)
    return certificate(json.loads(out.read_bytes()),seconds=5,conflicts=20000)

def codec_objects(s):
    row,rows,cols=s['row'],s['rows'],s['columns']
    enc=lambda v:call(s['encode'],[v]);dec=lambda v:call(s['decode'],[v])
    prep=lambda h,c:call(s['prepend'],[h,c])
    left=dec(prep(var('head'),var('columns')))
    right=cons(rows,1,[var('head'),dec(var('columns'))])
    values=[f'v{i}'for i in range(len(s['fields']))];tails=[f'c{i}'for i in range(len(values))]
    h=cons(row,0,[var(v)for v in values]);c=cons(cols,0,[var(t)for t in tails])
    proof={'Cases':dict(variable='head',**{'from':left,'to':right},cases=[dict(bindings=values,proof={'Cases':dict(variable='columns',**{'from':dec(prep(h,var('columns'))),'to':cons(rows,1,[h,dec(var('columns'))])},cases=[dict(bindings=tails,proof=convert(dec(prep(h,c)),cons(rows,1,[h,dec(c)])))])})])}
    lemma=entry('theorem',MATH,{'declaration':{'Theorem':dict(params=[['head',{'Data':row}],['columns',{'Data':cols}]],conditions=[],**{'from':left,'to':right},proof=proof)}},list(s['entries']),parameters={'head':{'Data':row},'columns':{'Data':cols}})
    lemma_id=identity(lemma);xs=var('rows');nil=cons(rows,0,[]);node=cons(rows,1,[var('head'),var('tail')])
    lhs=lambda x:dec(enc(x))
    step=trans(convert(lhs(node),dec(prep(var('head'),enc(var('tail'))))),{'Use':dict(theorem=lemma_id,arguments=[var('head'),enc(var('tail'))],premises=[])},{'Construct':dict(datatype=rows,constructor=1,arguments=[{'Refl':var('head')},{'Hypothesis':0}])})
    theorem=entry('theorem',MATH,{'declaration':{'Theorem':dict(params=[['rows',{'Data':rows}]],conditions=[],**{'from':lhs(xs),'to':xs},proof={'Induction':dict(variable='rows',**{'from':lhs(xs),'to':xs},cases=[dict(bindings=[],proof=convert(lhs(nil),nil)),dict(bindings=['head','tail'],proof=step)])})}},[lemma_id,*s['entries']],parameters={'rows':{'Data':rows}})
    return [*s['entries'].values(),lemma,theorem],identity(theorem)

def base(source,buffers='scoped'):
    return dict(schema=1,semantics='ink-physical-plan-v1',input_core_sha256=source,buffers=buffers,tables='ordered',borrow_reads=[],borrow_rows=[],definitions='shared',packed_datatypes=[],memo_functions=[],columns=[])

def produce(source,compiler,directory,records=(),bits=0,bounds=True,buffers='direct',source_core=False,page_size=None):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True);source=Path(source).resolve();compiler=Path(compiler).resolve()
    flags=['--core']if source_core else []
    with tempfile.TemporaryDirectory(prefix='ink-capabilities-')as temp:
        scratch=Path(temp);goals=scratch/'goals.json'
        # Owner and codec-only plans need source identity. Optional read and
        # unchanged-field analyses must not prevent independently admitted
        # representation choices; omitting them grants no such capabilities.
        if not bounds:
            core=scratch/'core.json'
            receipt=json.loads(invoke(compiler,'emit-core',source,*flags,'-o',core))
            subjects=dict(source=receipt['core_sha256'],obligations=[],map_obligations=[])
        else:
            invoke(compiler,'emit-bounds-obligations',source,*flags,'-o',goals)
            subjects=json.loads(goals.read_bytes())
        objects=[];read_ids=[];declined=[]
        for g in subjects['obligations']if bounds else []:
            try:
                goal={k:g[k]for k in ['params','conditions','from','to']}
                proof=bit_proof(compiler,scratch,goal)
                obj=entry('definition',READ,dict(source=subjects['source'],site=g['site'],obligation_sha256=identity(g),proof=proof));objects.append(obj);read_ids.append(identity(obj))
            except (ValueError,subprocess.TimeoutExpired)as e:declined.append(dict(site=g['site'],reason=str(e)))
        layouts=[];packing_proofs={}
        for record in sorted(set(records)):
            schema=scratch/'schema.json';invoke(compiler,'emit-column-codec',source,*flags,'--entry',record,'-o',schema)
            s=json.loads(schema.read_bytes());codec,root=codec_objects(s);objects.extend(codec);packing={}
            for field,t in s['fields']:
                width=0 if page_size is not None else 1 if t=='Bool'else min(bits,32 if t=='U32'else 64)if t in ['U32','U64']else 0
                if width:
                    mask=(1<<width)-1;v=var('value');binary=lambda op,a,b:{'Binary':dict(op=op,left=a,right=b)}
                    goal=dict(params=[['value','U64']],conditions=[dict(**{'from':binary('<=',v,{'U64':mask}),'to':{'Bool':True}})],**{'from':binary('&',v,{'U64':mask}),'to':v})
                    if width not in packing_proofs:packing_proofs[width]=bit_proof(compiler,scratch,goal)
                    packing[field]=dict(bits=width,proof=packing_proofs[width])
            layout=dict(record=record,roundtrip=root,packing=packing)
            if page_size is not None:layout['page_size']=page_size
            layouts.append(layout)
        # Canonical bytes and authenticated membership do not establish validity.
        objects=list({identity(o):o for o in objects}.values());store=Store.publish(directory,objects)
        plan=base(subjects['source'],buffers)
        if read_ids:plan['bounds']=dict(knowledge=store.bundle(read_ids))
        for l in layouts:l['knowledge']=store.bundle([l['roundtrip']])
        plan['columns']=layouts;write(scratch/'physical.json',plan)
        invoke(compiler,'check-physical-plan',source,scratch/'physical.json',*flags)
        map_ids=[];map_objects=[]
        for g in subjects['map_obligations']:
            if g['record']not in records:continue
            obj=entry('definition',MAP,dict(source=subjects['source'],site=g['site'],field=g['field'],obligation_sha256=identity(g),proof='Normalize'))
            trial=Store.publish(scratch/'map-proposal',[obj]);candidate=dict(plan,column_maps=dict(knowledge=trial.bundle([identity(obj)])))
            try:write(scratch/'physical.json',candidate);invoke(compiler,'check-physical-plan',source,scratch/'physical.json',*flags)
            except ValueError as e:declined.append(dict(site=g['site'],field=g['field'],reason=str(e)));continue
            map_ids.append(identity(obj));map_objects.append(obj)
        if map_objects:
            store=store.extend(map_objects)
            plan['column_maps']=dict(knowledge=store.bundle(map_ids))
        # Reissue all bundles against the final pinned snapshot.
        if read_ids:plan['bounds']=dict(knowledge=store.bundle(read_ids))
        for l in layouts:l['knowledge']=store.bundle([l['roundtrip']])
        write(directory/'physical.json',plan);invoke(compiler,'check-physical-plan',source,directory/'physical.json',*flags)
        write(directory/'plan.json',dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=subjects['source'],steps=[dict(kind='physical',package=plan)]))
        write(directory/'production.json',dict(schema=1,source=subjects['source'],reads=len(read_ids),unchanged_fields=len(map_ids),columns=len(layouts),declined=declined))
        return plan

def persistent_records(program):
    """Discover flat sequence elements reachable from retained source roots."""
    result=set();seen=set();records=program['records']
    def walk(t):
        if not isinstance(t,dict):return
        if 'Named'in t:
            name=t['Named']
            if name in seen:return
            seen.add(name)
            for _,field in records.get(name,[]):walk(field)
        elif 'List'in t:
            element=t['List']
            if element in ['U32','U64','Bool']:result.add('@'+element)
            elif isinstance(element,dict)and 'Named'in element:
                name=element['Named'];fields=records.get(name,[])
                if 1<=len(fields)<=16 and all(ty in ['U32','U64','I32','F32','Bool']for _,ty in fields):result.add(name)
            walk(element)
        else:
            for child in t.values():
                for value in child if isinstance(child,list)else[child]:walk(value)
    for state in program['states']:walk(state['ty'])
    return sorted(result)

def paged_record_groups(records,scalar_columns=(True,False)):
    # A scalar element type can occur in both retained large arrays and tiny
    # message fields. Keep a record-only choice so search can price that cost.
    seen=set()
    for scalars in scalar_columns:
        if type(scalars)is not bool:raise ValueError('scalar column choices must be boolean')
        group=tuple(sorted(n for n in records if scalars or not n.startswith('@')))
        if group and group not in seen:
            seen.add(group);yield ('all'if scalars else'records'),list(group)

def candidates(context,records=None,bits=(0,8),page_sizes=(64,256),page_scalar_columns=(True,False),buffer_strategies=('direct',),table_strategies=('ordered','indexed_slots')):
    if context.get('representation')or context.get('emit_target','rust')not in {'rust','rust-wasm'}:
        yield dict(status='declined',label='source-capabilities',reason='requires source Rust/Rust-Wasm carrier');return
    with tempfile.TemporaryDirectory(prefix='ink-capability-recipe-')as temp:
        d=Path(temp);source=write(d/'source.json',context['core'])
        # Price elementary storage choices independently of column conversion.
        # Otherwise a profitable owner strategy can be hidden by an expensive
        # transposed layout bundled into the same proposal.
        for buffers in buffer_strategies:
            if buffers not in ['scoped','direct']:raise ValueError('unknown buffer strategy')
            for tables in table_strategies:
                if tables not in ['ordered','indexed_slots']:raise ValueError('unknown table strategy')
                plan=base(context['source'],buffers);plan['tables']=tables
                yield dict(status='proposal',label=f'source-capabilities/storage/{buffers}/{tables}',step=dict(kind='physical',package=plan))
        paged_records=persistent_records(context['core']['program'])if records is None else records
        if records is None:
            records=[n for n,fields in context['core']['program']['records'].items()if 1<=len(fields)<=16 and all(t in ['U32','U64','I32','F32','Bool']for _,t in fields)]
        for width in bits:
            try:
                plan=produce(source,context['compiler'],d/str(width),records,width,source_core=True)
                yield dict(status='proposal',label=f'source-capabilities/{width}',step=dict(kind='physical',package=plan))
            except (ValueError,ImportError,subprocess.TimeoutExpired)as e:yield dict(status='declined',label='source-capabilities',reason=str(e))
        for page_size in page_sizes:
            for group,fields in paged_record_groups(paged_records,page_scalar_columns):
                try:
                    plan=produce(source,context['compiler'],d/('paged-'+group+'-'+str(page_size)),fields,0,bounds=False,source_core=True,page_size=page_size)
                    yield dict(status='proposal',label=f'source-capabilities/paged/{group}/{page_size}',step=dict(kind='physical',package=plan))
                except (ValueError,ImportError,subprocess.TimeoutExpired)as e:yield dict(status='declined',label='source-capabilities/paged/'+group,reason=str(e))

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source',type=Path);p.add_argument('-o',type=Path,required=True);p.add_argument('--compiler',type=Path,default=compiler_path());p.add_argument('--record',action='append',default=[]);p.add_argument('--bits',type=int,choices=[0,8,16,32,64],default=0);p.add_argument('--page-size',type=int,choices=[16,32,64,128,256,512,1024,2048,4096]);p.add_argument('--no-bounds',action='store_true');p.add_argument('--buffers',choices=['scoped','direct'],default='direct');p.add_argument('--core',action='store_true');a=p.parse_args()
    produce(a.source,a.compiler,a.o,a.record,a.bits,not a.no_bounds,a.buffers,a.core,a.page_size)
    print((a.o/'production.json').read_text())
if __name__=='__main__':main()
