"""Untrusted finite argument specialization with explicit equality guards."""
import copy,json,subprocess,tempfile
from pathlib import Path
from producers.point_delta import binary,sub
from producers.action_replacement import var
from producers.workspace import compiler_path
from producers.bitvector_proofs import certificate


def specialize_cache(original,arguments,directory):
    parameters=original['params'][2:]
    if not 1<=len(parameters)<=4 or not isinstance(arguments,list) or len(arguments)!=len(parameters):
        raise ValueError('hot cache requires one to four exact scalar arguments')
    terms=[]
    for (_,sort),argument in zip(parameters,arguments):
        if sort=='U64' and type(argument)is int and 0<=argument<1<<64:terms.append({'U64':argument})
        elif sort=='Bool' and type(argument)is bool:terms.append({'Bool':argument})
        else:raise ValueError('hot cache argument does not match the source scalar sort')
    guard={'Bool':True}
    for (name,_),term in reversed(list(zip(parameters,terms))):
        equal=binary('==',var(name),term)
        guard=equal if guard=={'Bool':True}else binary('&&',equal,guard)
    equalities=[]
    Path(directory).parent.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='parameter-proofs-',dir=Path(directory).parent)as scratch:
        d=Path(scratch)
        for i,((name,_),term)in enumerate(zip(parameters,terms)):
            goal=dict(params=parameters,conditions=[{'from':guard,'to':{'Bool':True}}],**{'from':var(name),'to':term})
            path=d/(str(i)+'.goal.json');cnf=d/(str(i)+'.cnf.json');path.write_text(json.dumps(goal))
            subprocess.run([str(compiler_path()),'bitvector-obligation',str(path),'--circuit','shared-v2','-o',str(cnf)],capture_output=True,check=True,timeout=15)
            proof=certificate(json.loads(cnf.read_text()),seconds=5,total_seconds=5)
            equalities.append((name,term,{'BitVector':dict(**{'from':var(name),'to':term},hypotheses=[0],certificate=proof)}))
    cache=copy.deepcopy(original);cache['params']=cache['params'][:2]
    cache['case']['normal']=sub(cache['case']['normal'],{name:term for (name,_),term in zip(parameters,terms)})
    return cache,guard,equalities


def candidates(model,limit=4):
    """Bounded proposal hints only. Values never become source assumptions.

    Prefer common boundary values and literal words already in the module. The
    command-line author can select any exact tuple; these are search seeds.
    """
    if type(limit)is not int or not 1<=limit<=16:raise ValueError('parameter candidate budget')
    constants={0,1}
    def literals(node):
        if isinstance(node,dict):
            value=node.get('U64')
            if type(value)is int and 0<=value<1<<64:constants.add(value)
            for child in node.values():literals(child)
        elif isinstance(node,list):
            for child in node:literals(child)
    from producers.representations import unchanged_query
    for action in model['actions'].values():literals(action['case']['normal'])
    words=sorted(constants)[:4];count=0
    for name,action in model['actions'].items():
        parameters=action['params'][2:]
        if not unchanged_query(model,action)or not 1<=len(parameters)<=4:continue
        if any(sort not in ('U64','Bool')for _,sort in parameters):continue
        domains=[words if sort=='U64'else[False,True]for _,sort in parameters]
        seen=set()
        for index in range(max(map(len,domains))):
            arguments=[values[index%len(values)]for values in domains];key=json.dumps(arguments)
            if key in seen:continue
            seen.add(key);yield name,arguments;count+=1
            if count>=limit:return
