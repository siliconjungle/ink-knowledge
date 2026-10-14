"""Database-authored typed implementation templates. No rewrite authority.

A template supplies ordinary core definitions and an ordinary equality proof.
The generic producer instantiates types, namespaces globals, and emits composed
extension/rewrite steps. The kernel independently checks every stage.
"""
import copy,json,subprocess,tempfile
from pathlib import Path
from .store import Store,entry,semantic_entry,canonical,identity
from .law_templates import infer,substitute_types
from .proposal_views import ProposalViews
SEMANTICS='ink-source-algorithm-v1'
EXTENSION='ink-source-extension-v1'

def namespace(value,names,bound=frozenset()):
    if isinstance(value,list):return [namespace(x,names,bound)for x in value]
    if not isinstance(value,dict):return copy.deepcopy(value)
    out={k:namespace(v,names,bound)for k,v in value.items()}
    if {'params','body','name'}<=set(value):out['body']=namespace(value['body'],names,bound|{n for n,_ in value['params']})
    if 'Lambda'in value and isinstance(value['Lambda'],list):
        n,body=value['Lambda'];out['Lambda']=[n,namespace(body,names,bound|{n})]
    if 'Let'in value:
        n,annotation,initial,body=value['Let'];out['Let']=[n,namespace(annotation,names,bound),namespace(initial,names,bound),namespace(body,names,bound|{n})]
    if 'Field'in value:
        receiver,field=value['Field']
        if isinstance(receiver,dict)and set(receiver)=={'Var'}and receiver['Var']in names and receiver['Var']not in bound:out['Field'][0]={'Var':names[receiver['Var']]}
    if set(value)=={'Named'}:out['Named']=names.get(value['Named'],value['Named'])
    for key in ['Call','Record']:
        if key in value and isinstance(value[key],list):out[key][0]=names.get(value[key][0],value[key][0])
    for key in ['Var','Enum']:
        if key in value and isinstance(value[key],str)and '.'in value[key]:
            first,rest=value[key].split('.',1)
            if first in names and first not in bound:out[key]=names[first]+'.'+rest
    if 'Op'in value:
        op=value['Op'][0]
        for prefix in ['call:','record:']:
            if op.startswith(prefix) and op[len(prefix):]in names:out['Op'][0]=prefix+names[op[len(prefix):]]
    return out

def instantiate(payload,bindings,ident,external=None):
    defs=substitute_types(payload['definitions'],bindings);law=substitute_types(payload['law'],bindings)
    globals_=[f['name']for f in defs['functions']]+defs.get('ids',[])+list(defs.get('records',{}))+list(defs.get('enums',{}))
    if len(set(globals_))!=len(globals_):raise ValueError('algorithm globals are not unique')
    prefix='db_'+ident[:12]+'_'+identity(bindings)[:12]+'_'
    names={n:prefix+n for n in globals_}
    if set(names)&set(external or {}):raise ValueError('algorithm import shadows local global')
    names.update(external or {});defs=namespace(defs,names);law=namespace(law,names)
    for f in defs['functions']:f['name']=names[f['name']]
    defs['ids']=[names[n]for n in defs.get('ids',[])]
    for key in ['records','enums']:defs[key]={names[n]:v for n,v in defs.get(key,{}).items()}
    return defs,law

def resolve(store,payload,bindings,ident,active=(),_cache=None,_budget=None):
    """Compose imported algorithms as data; all definitions/proofs still check.

    Imports export explicitly named globals and a reusable equality proof.
    The dependency graph is bounded, cycle checked and snapshot authenticated.
    """
    if ident in active or len(active)>=16:raise ValueError('algorithm import cycle/depth')
    if _cache is None:_cache={}
    if _budget is None:_budget=[1024]
    _budget[0]-=1
    if _budget[0]<0:raise ValueError('algorithm import traversal budget')
    key=identity([ident,bindings])
    if key in _cache:return copy.deepcopy(_cache[key])
    if set(payload)-{'type_parameters','definitions','law','imports'} or not {'type_parameters','definitions','law'}<=set(payload):raise ValueError('algorithm template fields')
    types=payload['type_parameters']
    if not isinstance(types,list)or len(types)>8 or any(not isinstance(t,str)or not t.isidentifier()for t in types)or len(set(types))!=len(types):raise ValueError('algorithm type parameters')
    if set(bindings)!=set(payload['type_parameters']):raise ValueError('algorithm type bindings')
    imports=payload.get('imports',{})
    if not isinstance(imports,dict) or len(imports)>32:raise ValueError('algorithm import budget')
    merged=dict(functions=[],ids=[],records={},enums={});external={};supports={};labels={}
    def merge(defs):
        for field in ('functions','ids','records','enums'):
            if field in ('records','enums'):
                for name,value in defs[field].items():
                    if name in merged[field] and merged[field][name]!=value:raise ValueError('algorithm type conflict')
                    merged[field][name]=value
            else:
                known={x['name']:x for x in merged[field]} if field=='functions' else {x:x for x in merged[field]}
                for value in defs[field]:
                    name=value['name'] if field=='functions' else value
                    if name in known and known[name]!=value:raise ValueError('algorithm definition conflict')
                    if name not in known:merged[field].append(value);known[name]=value
        if len(merged['functions'])+len(merged['records'])+len(merged['enums'])+len(merged['ids'])>256:raise ValueError('algorithm definition budget')
    for label,spec in sorted(imports.items()):
        if not isinstance(label,str)or not label.startswith('$')or set(spec)!={'algorithm','types','exports'}:raise ValueError('algorithm import fields')
        obj=store.object(spec['algorithm'])
        if obj['kind']!='definition'or obj['semantics']!=SEMANTICS:raise ValueError('algorithm import role')
        child_bindings=substitute_types(spec['types'],bindings)
        defs,law,nested=resolve(store,obj['payload'],child_bindings,spec['algorithm'],(*active,ident),_cache,_budget)
        merge(defs);supports.update(nested)
        token='$algorithm_'+identity([spec['algorithm'],child_bindings])
        supports[token]=law;labels[label]=token
        raw=obj['payload']['definitions']
        globals_=[f['name']for f in raw['functions']]+raw.get('ids',[])+list(raw.get('records',{}))+list(raw.get('enums',{}))
        prefix='db_'+spec['algorithm'][:12]+'_'+identity(child_bindings)[:12]+'_'
        if not isinstance(spec['exports'],dict):raise ValueError('algorithm export fields')
        for local,remote in spec['exports'].items():
            if not isinstance(local,str)or not local.isidentifier()or not isinstance(remote,str)or remote not in globals_ or local in external:raise ValueError('algorithm export conflict/unknown global')
            external[local]=prefix+remote
    own,law=instantiate(payload,bindings,ident,external);merge(own)
    def references(value):
        if isinstance(value,dict):return {k:labels.get(v,v)if k=='law'and isinstance(v,str)else references(v)for k,v in value.items()}
        if isinstance(value,list):return [references(v)for v in value]
        return value
    law=references(law)
    # Unknown labels fail here rather than accidentally naming another object.
    def uses(value):
        if isinstance(value,dict):
            for k,v in value.items():
                if k=='law'and isinstance(v,str)and v.startswith('$')and v not in supports:raise ValueError('unbound algorithm proof import')
                uses(v)
        elif isinstance(value,list):
            for v in value:uses(v)
    uses(law)
    _cache[key]=(merged,law,supports)
    return merged,law,supports

def materialise(law,supports,definition_context):
    """Bind imported equalities to the same exact executable definition image."""
    objects={};resolved={};active=set()
    def build(value):
        candidate=copy.deepcopy(value);dependencies=set(candidate.get('dependencies',[]))
        def walk(v):
            if isinstance(v,dict):
                result={}
                for k,x in v.items():
                    if k=='law'and isinstance(x,str)and x in supports:
                        if x in active:raise ValueError('algorithm proof dependency cycle')
                        if x not in resolved:
                            active.add(x);resolved[x]=build(supports[x]);active.remove(x)
                        result[k]=resolved[x];dependencies.add(resolved[x])
                    else:result[k]=walk(x)
                return result
            if isinstance(v,list):return [walk(x)for x in v]
            return v
        candidate=walk(candidate);candidate['definition_context']=definition_context;candidate['dependencies']=sorted(dependencies)
        obj=semantic_entry(candidate);lid=identity(obj);objects[lid]=obj
        if len(objects)>256:raise ValueError('algorithm proof closure budget')
        return lid
    return build(law),objects

def context(core,subject,roots):
    functions={f['name']:f for f in core['program']['functions']};names=set(functions);definitions={};active=set()
    def visit(name):
        if name in definitions:return
        if name in active or len(active)+len(definitions)>=128:raise ValueError('algorithm context depth/cycle')
        active.add(name);f=functions[name];body=subject['functions'][name];calls=set()
        def walk(t):
            if isinstance(t,dict):
                op=t.get('node',{}).get('Op')if isinstance(t.get('node'),dict)else None
                if op and op[0].startswith('call:') and op[0][5:]in names:calls.add(op[0][5:])
                for v in t.values():walk(v)
            elif isinstance(t,list):
                for v in t:walk(v)
        walk(body)
        for dep in sorted(calls):visit(dep)
        d=dict(params=f['params'],result=f['result'],body=body,callees={n:definitions[n]['sha256']for n in sorted(calls)})
        definitions[name]=dict(sha256=identity(d),definition=d);active.remove(name)
    for name in roots:visit(name)
    p=core['program'];result=dict(schema=1,definitions=definitions,records=p['records'],enums=p['enums'])
    if p['ids']:result['ids']=p['ids']
    return result

def proof_roots(core,law,added):
    """Retain original endpoint definitions as well as fresh helper bodies.

    A proof may unfold the existing function it replaces. Its definition is
    required even when the new helper never calls that original function.
    """
    available={f['name']for f in core['program']['functions']};roots=set(added)
    def walk(v):
        if isinstance(v,dict):
            call=v.get('node',{}).get('Op')if isinstance(v.get('node'),dict)else None
            if call and call[0].startswith('call:')and call[0][5:]in available:roots.add(call[0][5:])
            for child in v.values():walk(child)
        elif isinstance(v,list):
            for child in v:walk(child)
    for key in ['from','to','conditions','proof']:walk(law.get(key))
    return sorted(roots)

def propose(context_,**_):
    from ink_planner.semantic_search import match,key
    from .template_matching import TemplateSites
    compiler=context_['compiler'];root=Path(context_['knowledge_root']);store=Store(root,root/'store/snapshots'/f"{context_['knowledge_snapshot']}.json")
    def invoke(*args):
        r=subprocess.run([compiler,*map(str,args)],capture_output=True,text=True,timeout=context_.get('check_timeout',120))
        if r.returncode:raise ValueError(r.stderr[-2000:])
        return json.loads(r.stdout)if r.stdout.lstrip().startswith(('{','['))else r.stdout
    if not store.query(kind='definition',semantics=SEMANTICS,limit=1):return
    with tempfile.TemporaryDirectory(prefix='ink-source-algorithms-')as tmp:
        d=Path(tmp);original=d/'input.json';original.write_bytes(canonical(context_['core']));subjectfile=d/'subject.json';invoke('emit-semantic',original,'--core','-o',subjectfile);subject=json.loads(subjectfile.read_bytes())
        from .template_index import candidates
        sites_index=TemplateSites(subject);selected=candidates(store,subject,SEMANTICS,sites=sites_index);produced=0
        for at in range(0,len(selected),64):
            page=selected[at:at+64]
            for ident in page:
                try:
                    payload=store.object(ident)['payload']
                    if set(payload)-{'type_parameters','definitions','law','imports'} or not {'type_parameters','definitions','law'}<=set(payload):raise ValueError('algorithm template fields')
                    types=payload['type_parameters']
                    if len(types)>8 or len(set(types))!=len(types)or any(not isinstance(t,str)or not t.isidentifier()for t in types):raise ValueError('algorithm type parameters')
                    pattern=payload['law']['from'];params=payload['law']['params'];instances={}
                    for name,path,target,bindings in sites_index.matches(pattern,params,types):
                        instances.setdefault(key(bindings),(bindings,[]))[1].append((name,path,target))
                    for bindings,sites in instances.values():
                        definitions,law,supports=resolve(store,payload,bindings,ident)
                        current=context_['core']['program'];known={f['name']:f for f in current['functions']}
                        missing=copy.deepcopy(definitions)
                        missing['functions']=[]
                        for f in definitions['functions']:
                            if f['name']in known:
                                if known[f['name']]!=f:raise ValueError('existing algorithm definition changed')
                            else:missing['functions'].append(f)
                        for field in ['records','enums']:
                            missing[field]={}
                            for name,value in definitions[field].items():
                                if name in current[field]:
                                    if current[field][name]!=value:raise ValueError('existing algorithm type changed')
                                else:missing[field][name]=value
                        missing['ids']=[n for n in definitions['ids']if n not in current['ids']]
                        steps=[]
                        if any(missing.values()):
                            extension=entry('definition',EXTENSION,missing);eid=identity(extension)
                            transport=ProposalViews(store,{eid:extension},d/'extension')
                            request=dict(schema=1,semantics=EXTENSION,input_core_sha256=context_['source'],knowledge=transport.bundle([eid]),extension=eid)
                            requestfile=d/'extension.json';requestfile.write_bytes(canonical(request));extended=d/'extended.json'
                            receipt=invoke('extend-core',original,requestfile,'--core','-o',extended)
                            extendedcore=json.loads(extended.read_bytes());extendedsubject=d/'extended-subject.json';invoke('emit-semantic',extended,'--core','-o',extendedsubject)
                            extendedsubject=json.loads(extendedsubject.read_bytes());steps.append(dict(kind='extension',package=request))
                        else:
                            receipt=dict(core_sha256=context_['source']);extendedcore=context_['core'];extendedsubject=subject
                        definition_context=context(extendedcore,extendedsubject,proof_roots(extendedcore,law,[f['name']for f in definitions['functions']]))
                        lid,objects=materialise(law,supports,definition_context)
                        law=objects[lid]['payload'];view=ProposalViews(store,objects,d/'law').bundle([lid])
                        for name,path,target in sites:
                            arguments={}
                            if not match(law['from'],target,law['params'],arguments)or set(arguments)!=set(law['params']):continue
                            application=dict(function=name,path=list(path),law=lid,arguments=dict(sorted(arguments.items())),premises=['Normalize']*len(law['conditions']))
                            rewrite=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=receipt['core_sha256'],knowledge=view,applications=[application])
                            yield dict(status='proposal',label=ident,steps=steps+[dict(kind='rewrite',package=rewrite)])
                            produced+=1
                            if produced>=context_.get('candidate_limit',4096):return
                except (ValueError,KeyError,TypeError,OSError,subprocess.TimeoutExpired)as error:
                    yield dict(status='declined',label=ident,reason=str(error)[-2000:])


def publish(root,templates):
    """Publish authoring data; every concrete use still needs kernel admission."""
    objects=[];names={}
    for item in templates:
        obj=item['object']
        if obj['kind']!='definition'or obj['semantics']!=SEMANTICS:raise ValueError('source algorithm entry role')
        payload=obj['payload']
        if set(payload)-{'type_parameters','definitions','law','imports'} or not {'type_parameters','definitions','law'}<=set(payload):raise ValueError('source algorithm fields')
        refs=sorted({spec['algorithm']for spec in payload.get('imports',{}).values()})
        if not set(refs)<=set(obj['dependencies']):raise ValueError('source algorithm imports need canonical dependencies')
        objects.append(obj);names['source-algorithms/'+item['name']]=identity(obj)
    return Store(root).extend(objects,names)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description='Publish typed algorithm and proof templates')
    parser.add_argument('templates');parser.add_argument('--root',required=True);args=parser.parse_args()
    print(publish(args.root,json.loads(Path(args.templates).read_bytes())).snapshot_id)
