"""Ordinary typed probe authoring; program names and theorem IDs are irrelevant.

Inputs and workload weights propose profitability only. Bounded inhabited
recursive carriers use checked wire boundaries; effects still need lifecycle
profiles. The source checker independently proves each transformation edge.
"""
import copy, json, math, random
from importlib.resources import files
from .store import identity

PATTERNS = {'uniform-low','uniform-high','alternating','random','sparse-first','sparse-last'}
SCALARS = {'U32','I32','F32','Bool','String'}

def policy():
    value = json.loads(files('ink_knowledge').joinpath('automatic-selection.json').read_text())
    if value.get('schema') != 1 or not isinstance(value.get('scope'),str):raise ValueError('automatic selection policy schema')
    bounds = dict(functions=(1,16), calls=(1,512), candidates=(2,32), rounds=(9,64),
                  minimum_batch_ms=(1,50), maximum_calls_per_sample=(1,65536),
                  minimum_gain_percent=(1,50), confidence_percent=(90,99),
                  bootstrap_repetitions=(256,16384), expected_calls=(1,1000000000))
    for name,(lo,hi) in bounds.items():
        if type(value.get(name)) is not int or not lo<=value[name]<=hi:raise ValueError('automatic selection '+name)
    if not isinstance(value.get('sizes'),list) or not 1<=len(value['sizes'])<=8 or any(type(n)is not int or not 0<=n<=4096 for n in value['sizes']):raise ValueError('automatic selection sizes')
    if not isinstance(value.get('patterns'),list) or not value['patterns'] or not set(value['patterns'])<=PATTERNS:raise ValueError('automatic selection patterns')
    boundaries=value.get('boundaries',{})
    if not isinstance(boundaries,dict) or set(boundaries)!={'default','javascript','rust'}:raise ValueError('automatic selection boundary profiles')
    for target,modes in boundaries.items():
        if not isinstance(modes,list) or not modes or len(modes)!=len(set(modes)) or not set(modes)<={'trusted','portable','compact'}:raise ValueError('automatic selection boundary modes')
        if target!='javascript' and modes!=['trusted']:raise ValueError('unavailable boundary adapter')
    return value

def supported(t,records,active=(),wire=False):
    if isinstance(t,str):return t in SCALARS or wire and t in {'Unit','U64','Int'}
    if not isinstance(t,dict) or len(t)!=1:return False
    if 'List'in t:return supported(t['List'],records,active,wire)
    if wire and 'Option'in t:return supported(t['Option'],records,active,wire)
    if wire and 'Result'in t:
        pair=t['Result']
        return isinstance(pair,list) and len(pair)==2 and all(supported(x,records,active,wire)for x in pair)
    if wire and 'Vector'in t:
        pair=t['Vector']
        return isinstance(pair,list) and len(pair)==2 and type(pair[1])is int and 2<=pair[1]<=4 and pair[0]in ('U32','I32','F32')
    if 'Named'in t:
        name=t['Named']
        if name not in records:return False
        definition=records[name]
        if isinstance(definition,dict):
            return wire and (definition=={'id':True}or set(definition)=={'enum'}and isinstance(definition['enum'],list)and 0<len(definition['enum'])<=1024 and all(isinstance(v,str)for v in definition['enum']))
        if len(definition)>64:return False
        if name in active:return wire
        return all(supported(s,records,(*active,name),wire)for _,s in records[name])
    return False

def inhabited(t,records,active=()):
    """Finite constructor existence, independent of profitability or proof admission."""
    if isinstance(t,str):return supported(t,records,wire=True)
    if 'List'in t or 'Option'in t:return True
    if 'Vector'in t:return inhabited(t['Vector'][0],records,active)
    if 'Result'in t:return any(inhabited(x,records,active)for x in t['Result'])
    if 'Named'in t:
        name=t['Named']
        return name in records and (isinstance(records[name],dict)or name not in active and all(inhabited(x,records,(*active,name))for _,x in records[name]))
    return False

def create(core,target=None):
    p=policy();program=core['program'];records=dict(program.get('records',{}));declined=[]
    records.update({name:{'enum':variants}for name,variants in program.get('enums',{}).items()})
    records.update({name:{'id':True}for name in program.get('ids',[])})
    if program.get('states') or program.get('actions') or program.get('events'):
        return None,dict(reason='state/action/event lifecycle requires supplied workload evidence')
    constants=[]
    def walk(v):
        if isinstance(v,dict):
            n=v.get('Num')
            if type(n)in (int,float) and math.isfinite(n) and n>0:constants.append(n)
            for x in v.values():walk(x)
        elif isinstance(v,list):
            for x in v:walk(x)
    walk(program)
    pivot=min(constants,default=1)
    modes=p['boundaries'].get(target,p['boundaries']['default']);encoded=modes!=['trusted']
    pivot=max(1,min(pivot,65535));phases={};count=0;cells=0;function_count=0
    def boundaries(f):
        types=[t for _,t in f['params']]+[f['result']]
        return [mode for mode in modes if all(supported(t,records,wire=mode!='trusted')and inhabited(t,records)for t in types)]
    eligible=sum(bool(boundaries(f))for f in program['functions'])
    per_function=max(1,p['calls']//len(modes)//max(1,min(p['functions'],eligible)))
    def scalar(t,index,high=False):
        if t=='Unit':return None
        if t=='U64':return 18446744073709551615 if high else int(pivot) if index else 0
        if t=='Int':return {'Int':str(-(1<<100) if high else int(pivot) if index else 0)}
        if t=='Bool':return True if index else False
        if t=='String':return ['','probe','λ雪😀'][index%3]
        if t=='F32':return float(65536 if high else pivot if index else 0)
        if t=='I32':return -2147483648 if high else int(pivot) if index else 0
        return 4294967295 if high else int(pivot) if index else 0
    def atom(t,index,high=False,depth=0,active=(),width=None):
        nonlocal cells
        cells+=1
        if cells>1000000:raise ValueError('typed probe value budget')
        if depth>48:raise ValueError('probe carrier depth')
        bounded=any(active.count(name)>=4 for name in set(active))
        if isinstance(t,str):return scalar(t,index,high)
        if 'Named'in t:
            name=t['Named'];definition=records[name]
            if isinstance(definition,dict):
                if 'id'in definition:return format((1<<128)-1 if high else index,'032x')
                return name+'.'+definition['enum'][(index+int(high))%len(definition['enum'])]
            return {field:atom(s,index,high,depth+1,(*active,name),width)for field,s in definition}
        if 'List'in t:
            if bounded or not index:return []
            n=1
            if width is not None and not width[0]:width[0]=True;n=width[1]
            return [atom(t['List'],index,high,depth+1,active,width)for _ in range(n)]
        if 'Vector'in t:return [atom(t['Vector'][0],index,high,depth+1,active,width)for _ in range(t['Vector'][1])]
        if 'Option'in t:return {'None':None}if bounded or not index else {'Some':atom(t['Option'],index,high,depth+1,active,width)}
        if 'Result'in t:
            viable=[i for i,x in enumerate(t['Result'])if inhabited(x,records,active if bounded else ())]
            if not viable:raise ValueError('uninhabited probe carrier')
            side=viable[(index+int(high)+depth)%len(viable)]
            if bounded:side=min(viable,key=lambda i:len(json.dumps(t['Result'][i])))
            return {('Ok','Err')[side]:atom(t['Result'][side],index,high,depth+1,active,width)}
        raise ValueError('unsupported typed probe')
    def argument(t,n,pattern,rng):
        if not isinstance(t,dict) or 'List'not in t:
            return atom(t,0 if pattern in {'uniform-low','sparse-last'}else 1,pattern=='uniform-high',width=[False,n])
        inner=t['List'];items=[]
        for i in range(n):
            high=pattern=='uniform-high' or pattern=='alternating' and i%2==1
            index=0 if pattern=='uniform-low' else 1
            if pattern in {'sparse-first','sparse-last'}:index=int(i==(0 if pattern=='sparse-first' else n-1))
            item=atom(inner,index,high)
            if pattern=='random':
                def randomise(v):
                    if type(v)is bool:return bool(rng.getrandbits(1))
                    if type(v)is int:return rng.randrange(0,65536)
                    if type(v)is float:return rng.randrange(-256,256)/8
                    if isinstance(v,list):return [randomise(x)for x in v]
                    if isinstance(v,dict):return {k:randomise(x)for k,x in v.items()}
                    return v
                item=randomise(item)
            items.append(item)
        return items
    for function in program['functions']:
        function_modes=boundaries(function)
        if not function_modes:
            declined.append(dict(function=function['name'],reason='unsupported exact probe transfer type'));continue
        if function_count>=p['functions']:declined.append(dict(function=function['name'],reason='probe function budget'));continue
        calls=[];combinations=[(n,pattern)for n in p['sizes']for pattern in p['patterns']]
        indices=set(int(i*len(combinations)/min(per_function,len(combinations)))for i in range(min(per_function,len(combinations))))
        for index,(n,pattern)in enumerate(combinations):
                if index not in indices:continue
                if count+len(function_modes)>p['calls']:break
                rng=random.Random(0x1491+n)
                try:args=[argument(t,n,pattern,rng)for _,t in function['params']]
                except ValueError as error:
                    declined.append(dict(function=function['name'],reason=str(error)));break
                calls.append(dict(function=function['name'],args=args))
                count+=len(function_modes)
        if calls:
            function_count+=1
            for mode in function_modes:
                phase='call:'+function['name']+(':'+mode if encoded else '')
                phases[phase]=[dict(copy.deepcopy(c),**({'boundary':mode}if encoded else {}))for c in calls]
    if not phases:return None,dict(reason='no supported pure signatures',declined=declined)
    spec=dict(schema=3 if encoded else 1,phases=phases,profile={k:p['expected_calls']for k in phases},
              workload=dict(shape=dict(policy=identity(p),sizes=p['sizes']),distribution=dict(kind='synthetic typed probes',patterns=p['patterns']),
                            concurrency=1,residency='prepared source inputs; complete owned outputs and selected transfer boundaries'))
    return spec,dict(policy_sha256=identity(p),calls=count,functions=function_count,boundaries=modes,declined=declined,
                     scope=p['scope'])
