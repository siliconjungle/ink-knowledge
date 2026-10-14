"""Bounded untrusted collection/property discovery, outside the compiler.

Length/field/capture hints guide authoring and search. A hint is never a property
certificate: producers must supply an ordinary equality proof for admission.
"""
import copy

def unknown():return dict(length=None,bound=None,aliases=[],captures=[],ownership='unknown',fields={})
def analyse(program,function,node_budget=16384,helper_depth=32):
    functions={f['name']:f for f in program['functions']};work=[node_budget];active=set();summaries={}
    def input(name,ty,depth=0,seen=frozenset()):
        work[0]-=1
        if work[0]<0 or depth>32:return unknown()
        result=unknown();result['captures']=[name]
        if isinstance(ty,dict)and 'List'in ty:result.update(length=['input',name],bound=['input',name],aliases=[name],ownership='borrowed')
        if isinstance(ty,dict)and 'Named'in ty and ty['Named']not in seen:
            result['fields']={n:input(name+'.'+n,t,depth+1,seen|{ty['Named']})for n,t in program['records'].get(ty['Named'],[])}
        return result
    def merge(result,values):
        result['captures']=sorted({n for value in values for n in value['captures']});return result
    def walk(e,env,depth=0):
        work[0]-=1
        if work[0]<0 or depth>128 or not isinstance(e,dict):return unknown()
        if 'Var'in e:return copy.deepcopy(env.get(e['Var'],unknown()))
        if 'Record'in e:
            fields={n:walk(v,env,depth+1)for n,v in e['Record'][1]}
            return merge(dict(unknown(),fields=fields),fields.values())
        if 'Field'in e:
            receiver,name=e['Field'];value=walk(receiver,env,depth+1)
            return merge(copy.deepcopy(value['fields'].get(name,unknown())),[value])
        if 'Let'in e:
            name,_,value,body=e['Let'];value=walk(value,env,depth+1)
            result=walk(body,dict(env,**{name:value}),depth+1)
            return merge(result,[value,result])
        if 'Lambda'in e:
            name,body=e['Lambda'];local=dict(env);local.pop(name,None)
            return walk(body,local,depth+1)
        if 'Call'in e:
            name,args=e['Call'];values=[walk(a,env,depth+1)for a in args]
            if name=='choose'and len(values)==3:
                a,b=values[1:];out=unknown();out['aliases']=sorted(set(a['aliases']+b['aliases']))
                if a['length']==b['length']:out['length']=a['length']
                if a['bound']and b['bound']:out['bound']=['max',a['bound'],b['bound']]
                out['ownership']=a['ownership']if a['ownership']==b['ownership']else'unknown'
                out['fields']={n:v for n,v in a['fields'].items()if b['fields'].get(n)==v}
                return merge(out,values)
            if name in functions and name not in active and len(active)<helper_depth:
                f=functions[name];key=repr((name,values))
                if key in summaries:return copy.deepcopy(summaries[key])
                active.add(name);out=walk(f['body'],dict(zip([n for n,_ in f['params']],values)),depth+1);active.remove(name)
                if len(summaries)<128:summaries[key]=copy.deepcopy(out)
                return out
            return merge(unknown(),values)
        if 'Method'in e:
            receiver,method,args=e['Method'];value=walk(receiver,env,depth+1);out=unknown()
            if method in {'map','map_indexed','filter','sort','scan','concat','zip'}:
                out['ownership']='fresh';out['length']=value['length'];out['bound']=value['bound']
                if method=='filter':out['length']=None
                if method in {'concat','zip'}:
                    other=walk(args[0],env,depth+1);op='sum'if method=='concat'else'min'
                    for field in ['length','bound']:out[field]=[op,value[field],other[field]]if value[field]and other[field]else None
            captures=[value]
            for arg in args:
                if isinstance(arg,dict)and 'Lambda'in arg:
                    n,body=arg['Lambda'];local=dict(env);local.pop(n,None);captures.append(walk(body,local,depth+1))
                else:captures.append(walk(arg,env,depth+1))
            return merge(out,captures)
        values=[]
        for child in e.values():
            if isinstance(child,dict):values.append(walk(child,env,depth+1))
            elif isinstance(child,list):values.extend(walk(v,env,depth+1)for v in child if isinstance(v,dict))
        return merge(unknown(),values)
    f=functions[function];out=walk(f['body'],{n:input(n,t)for n,t in f['params']})
    out['scope']='untrusted source hints; mathematical certificates required';out['exhausted']=work[0]<0
    return out
