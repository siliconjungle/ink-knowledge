"""Knowledge-owned candidate families for recursive planning.

Every row is an untrusted proposal. All source, observation, migration, equality
and physical capability obligations must be replayed by the compiler.
"""
import copy, itertools, json, os, subprocess, tempfile, time
from pathlib import Path
from ink_knowledge import Store, identity, canonical
from ink_knowledge.store import entry

def row(kind,package,label):return dict(status='proposal',label=label,step=dict(kind=kind,package=package))
def decline(label,error):return dict(status='declined',label=label,reason=str(error)[-2000:])
def compiler(context,*args):
    result=subprocess.run([context['compiler'],*map(str,args)],capture_output=True,text=True,
        timeout=context.get('check_timeout',120))
    if result.returncode:raise ValueError(result.stderr[-2000:])
    return json.loads(result.stdout) if result.stdout.lstrip().startswith(('{','[')) else result.stdout

def published(context):
    """Discover canonical packages, raw source-bound representations and
    maintenance packages without relying on their author or discovery name."""
    from ink_knowledge.implementation_candidates import SEMANTICS
    source_objects=sorted((context.get('model')or{}).get('objects',[]))
    store=Store(context['knowledge_root'],Path(context['knowledge_root'])/'store/snapshots'/f"{context['knowledge_snapshot']}.json"if context.get('knowledge_snapshot')else None)
    # A per-snapshot binding index avoids loading every package body at every
    # admitted state; only entries bound to this source are opened.
    from ink_knowledge.published_bindings import bindings,source_key
    wanted=source_key(source_objects)
    for kind,entries in bindings(store).items():
        target=wanted if kind=='representation' else context['source']
        for ident,binding in entries:
            if binding!=target and not (kind=='maintenance' and binding is None):continue
            obj=store.object(ident)
            if kind=='representation':
                if obj['payload'].get('source_objects')!=source_objects:continue
                request=dict(schema=1,semantics=obj['semantics'],input_core_sha256=context['source'],
                    representation=ident,knowledge=store.bundle([ident]))
                yield row('representation',request,'published/'+ident)
                continue
            package=obj['payload'].get('package')
            if not isinstance(package,dict):
                if kind=='maintenance':yield decline('maintenance/'+ident,'entry must supply a checked source package or be a dependency of a representation')
                continue
            if package.get('input_core_sha256')!=context['source']:continue
            if 'knowledge_ref'in package:
                roots=package['knowledge_ref']['roots'];package={k:v for k,v in package.items()if k!='knowledge_ref'}
                package['knowledge']=store.bundle(roots)
            if package['semantics']=='ink-compiled-plan-v1':yield dict(status='plan',label='published/'+ident,package=package)
            elif package['semantics']=='ink-evidence-v1':yield row('rewrite',package,'published/'+ident)
            elif package['semantics']in ('ink-source-representation-v1','ink-source-representation-v2'):yield row('representation',package,'published/'+ident)
            elif package['semantics']=='ink-maintained-fold-v1':yield row('maintained',package,'published/'+ident)
            else:yield decline('published/'+ident,'unsupported package protocol '+package['semantics'])

def action_coalescing(context,operations):
    from producers.action_replacement import produce
    core=context['core']
    def call(statement):
        expr=statement.get('Expr',{})if isinstance(statement,dict)else{}
        return expr.get('Method')if isinstance(expr,dict)else None
    variants=[]
    def walk_block(block,path):
        for index in range(len(block)-1):
            a,b=call(block[index]),call(block[index+1])
            if not a or not b or a[0]!=b[0]or not a[2]or not b[2]or a[2][0]!=b[2][0]:continue
            for rule in operations:
                if (a[1],b[1])==(rule['first'],rule['second']):variants.append((path,index+int(rule['drop']=='second')))
        for index,statement in enumerate(block):
            if 'If'in statement:
                for branch in [1,2]:walk_block(statement['If'][branch],path+[index,'If',branch])
    for index,action in enumerate(core['program']['actions']):walk_block(action['body'],['program','actions',index,'body'])
    for path,index in variants:
        selected=copy.deepcopy(core);block=selected
        for component in path:block=block[component]
        block.pop(index)
        try:
            with tempfile.TemporaryDirectory(prefix='ink-action-recipe-')as temporary:
                d=Path(temporary);source=d/'selected.json';source.write_bytes(canonical(selected)+b'\n');model=d/'model.json'
                compiler(context,'emit-action-model',source,'--core','-o',model)
                package=produce(context['model'],json.loads(model.read_bytes()),selected,d/'knowledge',context['knowledge_root'])
                yield row('rewrite',package,'action-coalescing/'+identity(selected))
        except (ValueError,KeyError,subprocess.CalledProcessError)as error:yield decline('action-coalescing',error)
def variants(context,parameters):
    queries=[a['name']for a in context['core']['program']['actions']if a['kind']=='Query']
    domains={'$query':queries,'$optional_query':[None,*queries],
        '$table':list(range(len(context['model']['tables']))),
        '$slots':context.get('slot_counts',[4,16,64]),'$width':context.get('pack_widths',[2,4,8]),
        '$hot_keys':[[],*[ [n]for n in sorted({x['Num']for x in walk(context['core']['program'])if isinstance(x,dict)and 'Num'in x})]]}
    def expand(value):
        if isinstance(value,str) and value.startswith('$'):return domains[value]
        if isinstance(value,list):return [list(v)for v in itertools.product(*(expand(x)for x in value))]
        return [value]
    keys=list(parameters)
    for values in itertools.product(*(expand(parameters[k])for k in keys)):
        yield dict(zip(keys,values))
def requests(result):
    if isinstance(result,dict)and 'request'in result:return [result['request']]
    if isinstance(result,dict) and 'requests'in result:return result['requests']
    return [result]
def author(context,parameters,generate):
    # These families author maintained state/action representations. A module
    # with only pure function roots has no stateful observation to accelerate;
    # a vacuous action proof does not make a pure callable implementation.
    program=context['core']['program']
    if not program['states']and not program['actions']:
        yield decline('stateful representations','source has no state/action roots; pure replacements require source-function equality')
        return
    for options in variants(context,parameters):
        label=json.dumps(options,sort_keys=True)
        try:
            with tempfile.TemporaryDirectory(prefix='ink-recipe-author-')as temporary:
                os.environ['INK_COMPILER']=context['compiler']
                result=generate(context['model'],Path(temporary),options)
                for i,request in enumerate(requests(result)):
                    yield row('representation',request,label+'/'+str(i))
        except (ValueError,KeyError,TypeError,NotImplementedError,ImportError,subprocess.CalledProcessError)as error:
            yield decline(label,error)

def representations(context,**parameters):
    from producers.representations import generate
    yield from author(context,parameters,lambda m,d,p:generate(m,d,**p))
def invariant_observations(context,**parameters):
    from producers.invariant_representations import generate
    yield from author(context,parameters,lambda m,d,p:generate(m,d,context['compiler'],**p))
def generic_index(context,**parameters):
    from producers.generic_indexed import generate
    yield from author(context,parameters,lambda m,d,p:generate(m,d,**p))
def partition(context,**parameters):
    from producers.partition_representation import generate
    yield from author(context,parameters,lambda m,d,p:generate(m,d,**p))
def packed(context,**parameters):
    from producers.packed_representations import generate
    yield from author(context,parameters,lambda m,d,p:generate(m,d,compiler=Path(context['compiler']),**p))
def sequence_tree(context,**parameters):
    from producers.source_sequence_tree import generate
    yield from author(context,parameters,lambda m,d,p:generate(m,d,**p))
def scalar(context,**parameters):
    from producers.scalar_representation import generate
    yield from author(context,parameters,lambda m,d,p:generate(m,d,**p))
def compact(context):
    from producers.compact_observation import attach
    current=context.get('representation')
    if current is None:yield decline('compact observer','requires a representation');return
    try:
        with tempfile.TemporaryDirectory(prefix='ink-compact-recipe-')as temporary:
            yield row('representation',attach(current,Path(temporary)),'compact observer')
    except (ValueError,KeyError)as error:yield decline('compact observer',error)
def residual(context):
    from producers.residual_execution import generate
    current=context.get('representation')
    if current is None:yield decline('residual execution','requires a representation');return
    for action in [None,*context['model']['actions']]:
        try:
            with tempfile.TemporaryDirectory(prefix='ink-residual-recipe-')as temporary:
                request=generate(context['model'],current,Path(temporary),action)
                yield row('representation',request,'residual execution/'+str(action))
        except (ValueError,KeyError,TypeError)as error:yield decline('residual execution/'+str(action),error)

def product(context):
    from producers.representation_product import generate
    current=context.get('representation')
    if current is None:yield decline('product','requires a representation');return
    for peer in context.get('representation_pool',[]):
        if peer['representation']==current['representation']:continue
        try:
            with tempfile.TemporaryDirectory(prefix='ink-product-recipe-')as temporary:
                yield row('representation',generate(context['model'],[current,peer],Path(temporary)),
                    'product/'+peer['representation'])
        except (ValueError,KeyError)as error:yield decline('product/'+peer['representation'],error)

def semantic(context):
    """The generic semantic planner discovers every typed rewrite root and all
    installed specialisers. No operation or theorem-name selector is added here.
    """
    with tempfile.TemporaryDirectory(prefix='ink-semantic-recipe-')as temporary:
        d=Path(temporary);core=d/'core.json';core.write_bytes(canonical(context['core'])+b'\n')
        out=d/'selection.json';store=Store(context['knowledge_root'],Path(context['knowledge_root'])/'store/snapshots'/f"{context['knowledge_snapshot']}.json"if context.get('knowledge_snapshot')else None)
        command=[context['python'],'-m','ink_planner.semantic_search','--compiler',context['compiler'],
            '--core',str(core),'--knowledge-root',context['knowledge_root'],
            '--snapshot',str(store.root/'store/snapshots'/f'{store.snapshot_id}.json'),
            '--budget',str(context.get('semantic_budget',4096)),
            '--alternatives',str(d/'alternatives.jsonl'),'--stream-alternatives','--time-seconds',str(context.get('semantic_seconds',600)),'--compact-output','-o',str(out),
            '--diagnostics',str(d/'diagnostics.json')]
        if context.get('semantic_rounds') is not None:command+=['--rounds',str(context['semantic_rounds'])]
        if context.get('properties'):
            properties=d/'properties.json';properties.write_bytes(canonical(context['properties']));command+=['--properties',str(properties)]
        count=0;position=0;pending=b'';started=time.monotonic()
        alternatives=d/'alternatives.jsonl'
        with (d/'stdout.log').open('wb')as stdout,(d/'stderr.log').open('wb')as stderr:
            process=subprocess.Popen(command,stdout=stdout,stderr=stderr)
            try:
                while True:
                    if alternatives.exists():
                        with alternatives.open('rb')as stream:
                            stream.seek(position);chunk=stream.read(128_000_001)
                        if len(chunk)>128_000_000:raise ValueError('semantic alternative byte budget')
                        position+=len(chunk);pending+=chunk
                        while b'\n'in pending:
                            line,pending=pending.split(b'\n',1);package=json.loads(line);count+=1
                            yield row('rewrite',package,'semantic alternative/'+identity(package))
                    if process.poll()is not None:
                        # A final read after observing exit consumes the flushed tail.
                        if alternatives.exists()and alternatives.stat().st_size>position:continue
                        break
                    if time.monotonic()-started>=context.get('proposal_timeout',600):
                        yield decline('semantic search','proposal process time budget');break
                    time.sleep(.02)
                if process.returncode not in (None,0):yield decline('semantic search',(d/'stderr.log').read_text()[-2000:])
                elif not count:yield decline('semantic search','fixed point within supplied search budget')
                # Near-miss observations explain matched laws the checker did not
                # admit. They are diagnostics, never proposals or proof authority.
                # A search cut off by this budget leaves its last periodic receipt.
                diagnostics=d/'diagnostics.json'
                if diagnostics.exists() and diagnostics.stat().st_size<=16_000_000:
                    try:value=json.loads(diagnostics.read_bytes())
                    except ValueError:value=None
                    if isinstance(value,dict):
                        yield dict(status='diagnostic',label='semantic search',diagnostics=value)
            finally:
                if process.poll()is None:process.kill()
                process.wait()

def first_order_match(pattern,term,parameters,bindings):
    if isinstance(pattern,dict)and set(pattern)=={'Var'}and pattern['Var']in parameters:
        name=pattern['Var']
        if name in bindings:return bindings[name]==term
        bindings[name]=copy.deepcopy(term);return True
    if type(pattern)!=type(term):return False
    if isinstance(pattern,dict):return pattern.keys()==term.keys()and all(first_order_match(pattern[k],term[k],parameters,bindings)for k in pattern)
    if isinstance(pattern,list):return len(pattern)==len(term)and all(first_order_match(a,b,parameters,bindings)for a,b in zip(pattern,term))
    return pattern==term
def replace_variables(term,bindings):
    from producers.point_delta import sub
    return sub(term,bindings)

def definitions(context):
    """Discover arbitrary concrete or parametric endpoint laws. Every Instance,
    condition and complete exported-function equality is checked independently."""
    from producers.schema_match import Matcher,prove
    from producers.action_replacement import trans,convert,call,var
    from producers.representations import refs
    current=context.get('representation')
    if current is None:yield decline('definitions','requires an executable representation');return
    plan=current['knowledge']['objects'][current['representation']]['payload']
    exports={plan['encode'],plan['decode']}
    for action in plan['actions'].values():exports.update([action['execute'],action['next'],action.get('compact',{}).get('observe',action['observe'])])
    store=Store(context['knowledge_root'],Path(context['knowledge_root'])/'store/snapshots'/f"{context['knowledge_snapshot']}.json"if context.get('knowledge_snapshot')else None);after=None
    mathematical={i:store.object(i)for i in store.members()if store.object(i)['semantics']=='first-order-inductive-equality-v1'}
    while True:
        page=store.query(kind='theorem',semantics='first-order-inductive-equality-v1',after=after,limit=256)
        for ident in page:
            law=store.object(ident)['payload'].get('declaration',{}).get('Theorem')
            if law is None:continue
            dependencies=store.bundle([ident])['objects']
            for export in exports:
                original=(context.get('definition_choices')or{}).get(export,export)
                function=current['knowledge']['objects'].get(original,{}).get('payload',{}).get('declaration',{}).get('Function')
                if function is None:continue
                args=[var(n)for n,_ in function['params']];source=call(original,args)
                bodies=[source]
                if function['recursive']is None:bodies.append(function['body'])
                for body in bodies:
                    matcher=Matcher(dependencies,current['knowledge']['objects']);bindings={}
                    if not matcher.term(law['from'],body,set(dict(law['params'])),bindings)or set(bindings)!=set(dict(law['params']))or not matcher.complete(dependencies):continue
                    target=replace_variables(matcher.instantiate(law['to']),bindings)
                    if target==source or target==body:continue
                    declaration={'Function':dict(params=function['params'],result=function['result'],body=target,recursive=None)}
                    obj=entry('definition','first-order-inductive-equality-v1',{'declaration':declaration},refs(declaration),parameters=dict(function['params']),result=function['result'])
                    replacement=identity(obj);objects={**current['knowledge']['objects'],**dependencies,replacement:obj}
                    premise=[];support=set()
                    for c in law['conditions']:
                        proof,used=prove(dict(**{'from':replace_variables(matcher.instantiate(c['from']),bindings),'to':replace_variables(matcher.instantiate(c['to']),bindings)}),mathematical,current['knowledge']['objects'])
                        premise.append(proof);support.update(used)
                    if support:objects.update(store.bundle(sorted(support))['objects'])
                    fields=dict(theorem=ident,arguments=[bindings[n]for n,_ in law['params']],premises=premise)
                    proof={'Instance':dict(fields,sorts=matcher.sorts,functions=matcher.functions,definitions=matcher.definitions,assumptions={})}if matcher.sorts or matcher.functions or matcher.definitions else{'Use':fields}
                    before=replace_variables(matcher.instantiate(law['from']),bindings)
                    proof=trans(convert(source,before),proof,convert(target,call(replacement,args)))
                    try:
                        with tempfile.TemporaryDirectory(prefix='ink-definition-recipe-')as temporary:
                            staged=Store.publish(temporary,objects.values());request=copy.deepcopy(current)
                            request['knowledge']=staged.bundle(sorted({current['representation'],ident,replacement,*support}))
                            yield row('definitions',dict(request=request,proposals=[dict(original=original,replacement=replacement,proof=proof)]),'definition/'+ident)
                    except (ValueError,KeyError)as error:yield decline('definition/'+ident,error)
        if len(page)<256:break
        after=page[-1]

def properties(context):
    from importlib.resources import files
    from ink_planner.semantic_search import match,substitute,condition_proof
    with tempfile.TemporaryDirectory(prefix='ink-properties-recipe-')as temporary:
        d=Path(temporary);core=d/'core.json';core.write_bytes(canonical(context['core'])+b'\n');out=d/'subject.json'
        compiler(context,'emit-semantic',core,'--core','-o',out)
        subject=json.loads(out.read_bytes());store=Store(context['knowledge_root'],Path(context['knowledge_root'])/'store/snapshots'/f"{context['knowledge_snapshot']}.json"if context.get('knowledge_snapshot')else None)
        probes=json.loads(files('ink_knowledge').joinpath('property-probes.json').read_bytes())['probes']
        signatures={f['name']:f for f in context['core']['program']['functions']}
        for name,body in subject['functions'].items():
            if name not in signatures:continue
            variable='__ink_property_subject'
            params=dict(signatures[name]['params'])
            while variable in params:variable+='_'
            for probe in probes:
                if probe['operator'] is None:query=body;observation=dict(sort=body['sort'],node={'Free':variable})
                else:
                    if probe['receiver']not in body['sort'].get('Value',{}):continue
                    query=dict(sort=probe['result'],node={'Op':[probe['operator'],[body]]})
                    observation=dict(sort=probe['result'],node={'Op':[probe['operator'],[dict(sort=body['sort'],node={'Free':variable})]]})
                after=None
                while True:
                    page=store.query(kind='rewrite',semantics='ink-conditional-laws-v1',result=query['sort'],after=after,limit=256)
                    for ident in page:
                        law=store.object(ident)['payload'];bindings={}
                        if not match(law['from'],query,law['params'],bindings)or set(bindings)!=set(law['params']):continue
                        target=substitute(law['to'],bindings)
                        if target==query:continue
                        from ink_planner.semantic_search import discovery_objects, selection_roots
                        bundle=store.bundle([ident]);objects=discovery_objects(store,[ident])
                        semantic={i:o['payload']for i,o in objects.items()if o['kind']=='rewrite'}
                        premises=[condition_proof(dict(**{'from':substitute(c['from'],bindings),'to':substitute(c['to'],bindings)}),dict(objects=semantic))for c in law['conditions']]
                        proof={'Use':dict(law=ident,arguments=bindings,premises=premises)}
                        roots=selection_roots([dict(law=ident,premises=premises)])
                        package=dict(schema=1,semantics='ink-source-properties-v1',input_core_sha256=context['source'],knowledge=store.bundle(roots),
                            facts=[dict(function=name,context=observation,subject_variable=variable,value=target,proof=proof)])
                        from producers.collection_analysis import analyse
                        proposal=row('properties',package,name+'/'+probe['id']+'/'+ident)
                        proposal['advisory']=analyse(context['core']['program'],name)
                        yield proposal
                    if len(page)<256:break
                    after=page[-1]

def walk(value):
    pending=[value]
    while pending:
        node=pending.pop();yield node
        if isinstance(node,dict):pending.extend(node.values())
        elif isinstance(node,list):pending.extend(node)
def lexical_reads(program,only_function=None):
    """Untrusted typed place discovery. The emitter still checks ownership and
    lifetimes; source-free names and scalar fields never become read sites."""
    result=set();functions={f['name']:f for f in program['functions']}
    def infer(e,env):
        if not isinstance(e,dict):return None
        if 'Var'in e:return env.get(e['Var'])
        if 'Record'in e:return {'Named':e['Record'][0]}
        if 'Field'in e:
            receiver,field=e['Field'];ty=infer(receiver,env)
            if isinstance(ty,dict)and 'Named'in ty:return dict(program['records'].get(ty['Named'],[])).get(field)
        if 'Call'in e:
            f=functions.get(e['Call'][0]);return f['result']if f else None
        if 'Method'in e:
            receiver,method,args=e['Method'];ty=infer(receiver,env)
            if method in {'filter','take','drop','concat','sort'}:return ty
            if method=='map'and isinstance(ty,dict)and 'List'in ty and args and 'Lambda'in args[0]:
                n,body=args[0]['Lambda'];out=infer(body,dict(env,**{n:ty['List']}));return {'List':out}if out else None
        return None
    def visit(e,env,want=None):
        if not isinstance(e,dict):return
        ty=infer(e,env)
        if set(e)&{'Var','Field'}and ty is not None:
            base=e;fields=[]
            while isinstance(base,dict)and 'Field'in base:base,field=base['Field'];fields.append(field)
            place=(base['Var'],fields)if isinstance(base,dict)and 'Var'in base else None
            if place and isinstance(env.get(place[0]),dict)and set(env[place[0]])&{'Named','List'}:result.add(identity(e))
        if 'Let'in e:
            name,annotation,value,body=e['Let'];visit(value,env,annotation)
            local=dict(env);local[name]=annotation or infer(value,env);visit(body,local,want);return
        if 'Call'in e and e['Call'][0]in {'foldr','foldl','fold_until'}:
            name,args=e['Call'];source=infer(args[0],env)
            if isinstance(source,dict)and 'List'in source and len(args)==(4 if name=='fold_until'else 3):
                accumulator=infer(args[1],env)or want
                for arg in args[2:]:
                    local=dict(env);body=arg
                    for parameter in [source['List'],accumulator]:
                        if not isinstance(body,dict)or 'Lambda'not in body:break
                        binder,body=body['Lambda'];local[binder]=parameter
                    visit(body,local,accumulator)
                visit(args[0],env);visit(args[1],env,accumulator);return
        if 'Lambda'in e:return

        if 'Method'in e:
            receiver,method,args=e['Method'];visit(receiver,env);ty=infer(receiver,env)
            for arg in args:
                if isinstance(arg,dict)and 'Lambda'in arg and isinstance(ty,dict)and 'List'in ty:
                    name,body=arg['Lambda'];visit(body,dict(env,**{name:ty['List']}))
                else:visit(arg,env)
            return
        for value in e.values():
            if isinstance(value,dict):visit(value,env)
            elif isinstance(value,list):
                for child in value:
                    if isinstance(child,dict):visit(child,env)
                    elif isinstance(child,list):
                        for nested in child:
                            if isinstance(nested,dict):visit(nested,env)
    for f in program['functions']:
        if only_function is None or f['name']==only_function:visit(f['body'],dict(f['params']),f['result'])
    return result
def physical(context, source_strategies, definition_strategies, composition_limit=256):
    from ink_knowledge.selectors import matches
    from itertools import product
    if type(composition_limit)is not int or not 1<=composition_limit<=4096:raise ValueError('physical composition budget')
    program=context['core']['program'];current=context.get('representation')
    reads=lexical_reads(program);rows=set();tables={s['name']for s in program['states']}
    for node in walk(program):
        if not isinstance(node,dict):continue
        if 'Try'in node:
            receiver=node['Try'].get('Method',[])
            if receiver and receiver[1]=='ok_or'and 'Method'in receiver[0]:
                base=receiver[0]['Method']
                if base[1]=='get'and base[0].get('Var')in tables:rows.add(identity(node))
        if 'Method'in node:
            receiver,name,_=node['Method']
            if name in {'map','filter'}and 'Method'in receiver:
                base=receiver['Method']
                if base[1]in {'values','get'}and base[0].get('Var')in tables:rows.add(identity(node))
    base=dict(tables='ordered',buffers='scoped',definitions='shared',borrow_reads=[],borrow_rows=[],packed_datatypes=[],memo_functions=[],reservations=(context.get('physical')or{}).get('reservations',[]))
    strategies=[base];target=context.get('emit_target','rust')
    if current is None:
        for strategy in source_strategies:
            if target not in strategy.get('targets',[]):continue
            if strategy.get('requires_tables',False)and not tables:continue
            strategies.append(dict(base,buffers=strategy.get('buffers','scoped'),tables=strategy['tables'],borrow_reads=sorted(reads)if strategy['borrow']else[],
                borrow_rows=sorted(rows)if strategy['borrow']else[]))
    if current is not None:
        ds=context.get('definitions',{});axes={}
        for strategy in definition_strategies:
            if target not in strategy.get('targets',[]):continue
            field=strategy['site_field']
            if field not in {'packed_datatypes','memo_functions'}:raise ValueError('physical capability field')
            sites=sorted(ident for ident,declaration in ds.items()if matches(strategy['eligible'],declaration))
            groups=([sites]if strategy['sites']=='all'else[[i]for i in sites])if sites else[]
            for group in groups:
                axes.setdefault(field,[]).append(group)
        # Capabilities compose independently. Candidate creation is bounded;
        # every complete composition still receives ordinary compiler checking.
        fields=sorted(axes);groups={f:list({tuple(g):g for g in axes[f]}.values())for f in fields}
        def singles(field):
            for group in groups[field]:yield {field:group}
        streams=[singles(f)for f in fields]
        if len(fields)>1:streams.append((dict(zip(fields,combination))for combination in product(*(groups[f]for f in fields))))
        count=0
        for batch in itertools.zip_longest(*streams):
            for choice in batch:
                if choice is None:continue
                if count>=composition_limit:break
                strategies.append(dict(base,definitions='selected',**choice));count+=1
            if count>=composition_limit:break
    seen=set()
    for strategy in strategies:
        plan=dict(schema=1,semantics='ink-physical-plan-v1',input_core_sha256=context['source'],**strategy)
        if current is not None:plan['representation']=current['representation']
        digest=identity(plan)
        if digest in seen:continue
        seen.add(digest);yield row('physical',plan,'physical/'+digest)

def routing(context):
    if context.get('emit_target')not in {'wgpu','webgpu'}:yield decline('routing','placement capability requires a GPU host target');return
    from ink_planner.source_routing import produce
    functions=context['core']['program']['functions']
    for function in functions:
        names=[f['name']for f in functions]
        for placements in [{},{n:'gpu'for n in names},*[{n:'gpu'}for n in names]]:
            package=produce(context['core'],context['source'],function['name'],placements)
            yield row('routing',dict(package=package),'routing/'+function['name']+'/'+identity(placements))

def whole_entry_routing(context,placements):
    if context.get('emit_target')not in {'wgpu','webgpu'}:yield decline('routing','placement capability requires a GPU host target');return
    from ink_planner.source_routing import produce
    for function in context['core']['program']['functions']:
        for mode in placements:
            package=produce(context['core'],context['source'],function['name'],{},baseline=True)
            package['stages'][0].update(backend='gpu'if mode=='gpu'else'rust',domain=mode)
            yield row('routing',dict(package=package),'whole-entry/'+function['name']+'/'+mode)

def migration(context):
    from producers.representation_bridge import generate
    current=context.get('representation')
    if current is None:yield decline('migration','requires a representation');return
    for peer in context.get('representation_pool',[]):
        if peer['representation']==current['representation']:continue
        for via_logical in [False,True]:
            try:
                with tempfile.TemporaryDirectory(prefix='ink-migration-recipe-')as temporary:
                    bridge=generate(current,peer,Path(temporary),via_logical=via_logical)
                    # Migration is an edge between independently checked plans,
                    # rather than an unproved change to a representation role.
                    yield dict(status='migration',label='migration/'+peer['representation'],source=current,target=peer,bridge=bridge)
            except (ValueError,KeyError)as error:yield decline('migration',error)


def point_access_cache(context):
    """Precise access hints discover candidates; universal equations admit them."""
    from producers.access_cache import discover
    from producers.representations import generate
    with tempfile.TemporaryDirectory(prefix='ink-point-access-') as temporary:
        d=Path(temporary);source=d/'source.json';access_path=d/'access.json'
        source.write_bytes(canonical(context['core'])+b'\n')
        try:
            compiler(context,'emit-access',source,'--core','-o',access_path)
            compiler(context,'check-access',source,access_path,'--core')
            access=json.loads(access_path.read_bytes())
            for query in discover(context['model'],access)[:2]:
                try:
                    os.environ['INK_COMPILER']=context['compiler']
                    result=generate(context['model'],d/query,cache_query=query,preserve_cache=True,access=access)
                    yield row('representation',result['requests'][1],'point-cache:'+query)
                except (ValueError,KeyError,TypeError,NotImplementedError) as error:yield decline('point-cache:'+query,error)
        except (ValueError,KeyError,OSError) as error:yield decline('point-access',error)


def contract_witnesses(context):
    """Find postcondition witnesses and replay every contract in the module."""
    if not context['core']['program'].get('contracts',{}).get('specifications'):return
    from producers.contract_candidates import propose
    with tempfile.TemporaryDirectory(prefix='ink-contract-recipe-') as temporary:
        directory=Path(temporary);core=directory/'core.json';core.write_bytes(canonical(context['core'])+b'\n')
        try:
            report=propose(context['compiler'],core,directory/'candidates')
            store=Store(directory/'candidates')
            for ident in report['candidates']:
                yield row('rewrite',store.object(ident)['payload']['package'],'contract/'+ident)
            for failure in report['rejected']:yield decline('contract/'+failure['specification'],failure['reason'])
        except (ValueError,subprocess.CalledProcessError) as error:yield decline('contract-witnesses',error)


def source_algorithms(context):
    from ink_knowledge.source_algorithms import propose
    yield from propose(context)
