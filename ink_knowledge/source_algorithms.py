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

def namespace(value,names):
    if isinstance(value,list):return [namespace(x,names)for x in value]
    if not isinstance(value,dict):return copy.deepcopy(value)
    out={k:namespace(v,names)for k,v in value.items()}
    if set(value)=={'Named'}:out['Named']=names.get(value['Named'],value['Named'])
    for key in ['Call','Record']:
        if key in value and isinstance(value[key],list):out[key][0]=names.get(value[key][0],value[key][0])
    for key in ['Var','Enum']:
        if key in value and isinstance(value[key],str)and '.'in value[key]:
            first,rest=value[key].split('.',1)
            if first in names:out[key]=names[first]+'.'+rest
    if 'Op'in value:
        op=value['Op'][0]
        if op.startswith('call:') and op[5:]in names:out['Op'][0]='call:'+names[op[5:]]
    return out

def instantiate(payload,bindings,ident):
    defs=substitute_types(payload['definitions'],bindings);law=substitute_types(payload['law'],bindings)
    globals_=[f['name']for f in defs['functions']]+defs.get('ids',[])+list(defs.get('records',{}))+list(defs.get('enums',{}))
    if len(set(globals_))!=len(globals_):raise ValueError('algorithm globals are not unique')
    prefix='db_'+ident[:12]+'_'+identity(bindings)[:12]+'_'
    names={n:prefix+n for n in globals_};defs=namespace(defs,names);law=namespace(law,names)
    for f in defs['functions']:f['name']=names[f['name']]
    defs['ids']=[names[n]for n in defs.get('ids',[])]
    for key in ['records','enums']:defs[key]={names[n]:v for n,v in defs.get(key,{}).items()}
    return defs,law

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

def propose(context_,**_):
    from ink_planner.semantic_search import positions,match,key
    compiler=context_['compiler'];root=Path(context_['knowledge_root']);store=Store(root,root/'store/snapshots'/f"{context_['knowledge_snapshot']}.json")
    def invoke(*args):
        r=subprocess.run([compiler,*map(str,args)],capture_output=True,text=True,timeout=context_.get('check_timeout',120))
        if r.returncode:raise ValueError(r.stderr[-2000:])
        return json.loads(r.stdout)if r.stdout.lstrip().startswith(('{','['))else r.stdout
    if not store.query(kind='definition',semantics=SEMANTICS,limit=1):return
    with tempfile.TemporaryDirectory(prefix='ink-source-algorithms-')as tmp:
        d=Path(tmp);original=d/'input.json';original.write_bytes(canonical(context_['core']));subjectfile=d/'subject.json';invoke('emit-semantic',original,'--core','-o',subjectfile);subject=json.loads(subjectfile.read_bytes())
        after=None;work=0;produced=0
        while True:
            page=store.query(kind='definition',semantics=SEMANTICS,after=after,limit=64)
            for ident in page:
                try:
                    payload=store.object(ident)['payload']
                    if set(payload)!={'type_parameters','definitions','law'}:raise ValueError('algorithm template fields')
                    types=payload['type_parameters']
                    if len(types)>8 or len(set(types))!=len(types)or any(not isinstance(t,str)or not t.isidentifier()for t in types):raise ValueError('algorithm type parameters')
                    pattern=payload['law']['from'];params=payload['law']['params'];instances={}
                    for name,body in subject['functions'].items():
                        for path,target in positions(body):
                            work+=1
                            if work>200_000:raise ValueError('algorithm matching budget')
                            bindings={}
                            if infer(pattern,target,params,types,bindings)and set(bindings)==set(types):instances.setdefault(key(bindings),(bindings,[]))[1].append((name,path,target))
                    for bindings,sites in instances.values():
                        definitions,law=instantiate(payload,bindings,ident)
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
                        law['definition_context']=context(extendedcore,extendedsubject,[f['name']for f in definitions['functions']])
                        obj=semantic_entry(law);lid=identity(obj);view=ProposalViews(store,{lid:obj},d/'law').bundle([lid])
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
            if len(page)<64:break
            after=page[-1]


def publish(root,templates):
    """Publish authoring data; every concrete use still needs kernel admission."""
    objects=[];names={}
    for item in templates:
        obj=item['object']
        if obj['kind']!='definition'or obj['semantics']!=SEMANTICS:raise ValueError('source algorithm entry role')
        payload=obj['payload']
        if set(payload)!={'type_parameters','definitions','law'}:raise ValueError('source algorithm fields')
        objects.append(obj);names['source-algorithms/'+item['name']]=identity(obj)
    return Store(root).extend(objects,names)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description='Publish typed algorithm and proof templates')
    parser.add_argument('templates');parser.add_argument('--root',required=True);args=parser.parse_args()
    print(publish(args.root,json.loads(Path(args.templates).read_bytes())).snapshot_id)
