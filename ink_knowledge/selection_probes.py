"""Ordinary typed probe authoring; program names and theorem IDs are irrelevant.

Inputs and workload weights propose profitability only. Unsupported recursive,
effectful or transfer types decline; the source checker still proves each edge.
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
    return value

def supported(t,records,active=()):
    if isinstance(t,str):return t in SCALARS
    if not isinstance(t,dict) or len(t)!=1:return False
    if 'List'in t:return supported(t['List'],records,active)
    if 'Vector'in t:return False # fixed shape transfer needs its explicit descriptor
    if 'Named'in t:
        name=t['Named']
        return name in records and len(records[name])<=64 and name not in active and all(supported(s,records,(*active,name))for _,s in records[name])
    return False

def create(core):
    p=policy();program=core['program'];records=program.get('records',{});declined=[]
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
    pivot=max(1,min(pivot,65535));phases={};count=0;cells=0
    def scalar(t,index,high=False):
        if t=='Bool':return True if index else False
        if t=='String':return ['','probe','λ雪😀'][index%3]
        if t=='F32':return float(65536 if high else pivot if index else 0)
        if t=='I32':return -2147483648 if high else int(pivot) if index else 0
        return 4294967295 if high else int(pivot) if index else 0
    def atom(t,index,high=False,depth=0):
        nonlocal cells
        cells+=1
        if cells>1000000:raise ValueError('typed probe value budget')
        if depth>8:raise ValueError('probe carrier depth')
        if isinstance(t,str):return scalar(t,index,high)
        if 'Named'in t:return {name:atom(s,index,high,depth+1)for name,s in records[t['Named']]}
        if 'List'in t:return [atom(t['List'],index,high,depth+1)]
        raise ValueError('unsupported typed probe')
    def argument(t,n,pattern,rng):
        if not isinstance(t,dict) or 'List'not in t:return atom(t,1)
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
        if not all(supported(t,records)for _,t in function['params']) or not supported(function['result'],records):
            declined.append(dict(function=function['name'],reason='unsupported exact probe transfer type'));continue
        if len(phases)>=p['functions']:declined.append(dict(function=function['name'],reason='probe function budget'));continue
        calls=[]
        for n in p['sizes']:
            for pattern in p['patterns']:
                if count>=p['calls']:break
                rng=random.Random(0x1491+n)
                calls.append(dict(function=function['name'],args=[argument(t,n,pattern,rng)for _,t in function['params']]))
                count+=1
        if calls:phases['call:'+function['name']]=calls
    if not phases:return None,dict(reason='no supported pure signatures',declined=declined)
    spec=dict(schema=1,phases=phases,profile={k:p['expected_calls']for k in phases},
              workload=dict(shape=dict(policy=identity(p),sizes=p['sizes']),distribution=dict(kind='synthetic typed probes',patterns=p['patterns']),
                            concurrency=1,residency='captured immutable inputs; complete owned outputs'))
    return spec,dict(policy_sha256=identity(p),calls=count,functions=len(phases),declined=declined,
                     scope=p['scope'])
