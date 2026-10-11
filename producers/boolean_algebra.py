"""Generic Boolean identities authored as small, checked truth-table proofs."""
import json
from producers.action_replacement import var, convert
from producers.point_delta import binary, sub


class Tactic:
    def __init__(self,add):self.add=add;self.cache={}
    def prove(self,a,z):
        atoms=[]
        def abstract(t):
            if 'Bool' in t:return t
            if 'Binary' in t and t['Binary']['op'] in ['&&','||']:
                x=t['Binary'];return binary(x['op'],abstract(x['left']),abstract(x['right']))
            if t not in atoms:atoms.append(t)
            return var('boolean_atom_'+str(atoms.index(t)))
        left,right=abstract(a),abstract(z)
        if len(atoms)>6:raise ValueError('Boolean authoring atom budget')
        key=json.dumps([left,right],sort_keys=True)
        params=[['boolean_atom_'+str(i),'Bool'] for i in range(len(atoms))]
        def cases(i,l,r):
            if i==len(params):
                def ground(t):
                    if 'Bool' in t:return t['Bool']
                    x=t['Binary'];a,b=ground(x['left']),ground(x['right'])
                    return a and b if x['op']=='&&' else a or b
                if ground(l)!=ground(r):raise ValueError('Boolean identity has a false truth-table branch')
                return convert(l,r)
            name=params[i][0]
            return {'BoolCases':dict(variable=name,**{'from':l,'to':r},
                on_false=cases(i+1,sub(l,{name:{'Bool':False}}),sub(r,{name:{'Bool':False}})),
                on_true=cases(i+1,sub(l,{name:{'Bool':True}}),sub(r,{name:{'Bool':True}})))}
        if key not in self.cache:
            self.cache[key]=self.add({'Theorem':dict(params=params,conditions=[],**{'from':left,'to':right},proof=cases(0,left,right))})
        return {'Use':dict(theorem=self.cache[key],arguments=atoms,premises=[])}
