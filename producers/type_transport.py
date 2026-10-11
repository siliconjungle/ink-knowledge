"""Structural transport of state-threading carriers, with ordinary round trips.

Application values whose fields do not contain logical roots keep their types.
The constructor/field definitions alone determine every generated adapter.
"""
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import match,sub


class Transport:
    def __init__(self,objects,add,fun,law,bases,rules):
        self.objects,self.add,self.fun,self.law,self.rules=objects,add,fun,law,rules
        self.types={d:value[0] for d,value in bases.items()}
        self.codecs={d:value[1:] for d,value in bases.items()}
    def sort(self,s):
        if not isinstance(s,dict):return s
        d=s['Data']
        if d not in self.types:
            declaration=self.objects[d]['payload']['declaration']['Datatype'];constructors=[];changed=False
            for c in declaration['constructors']:
                fields=[self.sort(f) for f in c['fields']];changed|=fields!=c['fields'];constructors.append(dict(name=c['name'],fields=fields))
            self.types[d]=self.add({'Datatype':dict(constructors=constructors)}) if changed else d
        return {'Data':self.types[d]}
    def codec(self,s):
        target=self.sort(s)
        if s==target:return None
        d=s['Data']
        if d not in self.codecs:
            constructors=self.objects[d]['payload']['declaration']['Datatype']['constructors'];physical=target['Data'];forward=[];backward=[]
            for i,c in enumerate(constructors):
                ns=['transport_'+str(j) for j in range(len(c['fields']))];encode=[];decode=[]
                for n,f in zip(ns,c['fields']):
                    adapter=None if f=='SelfType' else self.codec(f)
                    encode.append({'SelfCall':[var(n)]} if f=='SelfType' else call(adapter[0],[var(n)]) if adapter else var(n))
                    decode.append({'SelfCall':[var(n)]} if f=='SelfType' else call(adapter[1],[var(n)]) if adapter else var(n))
                forward.append((ns,cons(physical,i,encode)));backward.append((ns,cons(d,i,decode)))
            recursive=0 if any('SelfType' in c['fields'] for c in constructors) else None
            encode=self.fun([['transport',s]],target,match(var('transport'),forward),recursive)
            decode=self.fun([['transport',target]],s,match(var('transport'),backward),recursive)
            a,z=call(decode,[call(encode,[var('transport')])]),var('transport');cases=[]
            for i,c in enumerate(constructors):
                ns=['transport_'+str(j) for j in range(len(c['fields']))];parts=[];middle=[];hypothesis=0
                for n,f in zip(ns,c['fields']):
                    adapter=None if f=='SelfType' else self.codec(f)
                    if f=='SelfType':
                        middle.append(call(decode,[call(encode,[var(n)])]));parts.append({'Hypothesis':hypothesis});hypothesis+=1
                    elif adapter:
                        middle.append(call(adapter[1],[call(adapter[0],[var(n)])]));parts.append({'Use':dict(theorem=adapter[2],arguments=[var(n)],premises=[])})
                    else:middle.append(var(n));parts.append({'Refl':var(n)})
                bound=cons(d,i,[var(n) for n in ns]);proof=trans(convert(sub(a,{'transport':bound}),cons(d,i,middle)),{'Construct':dict(datatype=d,constructor=i,arguments=parts)})
                cases.append(dict(bindings=ns,proof=proof))
            roundtrip=self.law([['transport',s]],a,z,{'Induction':dict(variable='transport',**{'from':a,'to':z},cases=cases)})
            self.codecs[d]=(encode,decode,roundtrip);self.rules.append(roundtrip)
        return self.codecs[d]
    def to_physical(self,t,s):
        codec=self.codec(s);return call(codec[0],[t]) if codec else t
    def to_logical(self,t,s):
        codec=self.codec(s);return call(codec[1],[t]) if codec else t
    def infer(self,t,env):
        if 'Var' in t:return env[t['Var']][0]
        if 'Bool' in t:return 'Bool'
        if 'U64' in t:return 'U64'
        if 'Construct' in t:return {'Data':t['Construct']['datatype']}
        if 'Call' in t:return self.objects[t['Call']['function']]['payload']['declaration']['Function']['result']
        if 'If' in t:return self.infer(t['If']['on_true'],env)
        if 'Binary' in t:return 'U64' if t['Binary']['op'] in ['+','-','*','&','quot','rem','f32:+','f32:-','f32:*','f32:neg'] else 'Bool'
        if 'Match' in t:
            x=t['Match'];s=self.infer(x['scrutinee'],env);c=self.objects[s['Data']]['payload']['declaration']['Datatype']['constructors'][0];b=x['branches'][0]
            local={**env,**{n:(s if f=='SelfType' else f,s if f=='SelfType' else f) for n,f in zip(b['bindings'],c['fields'])}}
            return self.infer(b['body'],local)
        raise ValueError('unsupported typed action term')
