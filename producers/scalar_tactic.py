"""Untrusted finite scalar abstraction. Every result is a replayed ordinary law.

Opaque calls are typed parameters, never axioms about those calls. Instantiation
uses the kernel's ordinary Use rule and the exact supplied premise proofs.
"""
import hashlib,json,os,subprocess,tempfile
from pathlib import Path
from action_replacement import var
from bitvector_proofs import certificate

class Scalar:
    def __init__(self,add,sort,normal):
        self.add,self.sort,self.normal=add,sort,normal
        self.compiler=Path(os.environ.get('INK_COMPILER','target/debug/ink')).resolve()
        self.memo={}
    def prove(self,a,z,env,facts=()):
        for words in (False,True):
            try:return self._prove(a,z,env,facts,words)
            except ValueError as e:
                self.last_error=str(e)
                if not words:self.boolean_error=str(e)
        raise ValueError('scalar abstraction did not prove goal')
    def _prove(self,a,z,env,facts,words):
        opaque=[];sorts=[]
        def arithmetic(t):
            if isinstance(t,list):return any(arithmetic(v)for v in t)
            if not isinstance(t,dict):return False
            return ('Binary'in t and t['Binary']['op']in ('+','-','*'))or any(arithmetic(v)for v in t.values())
        keep_arithmetic=arithmetic(a)or arithmetic(z)
        def abstract(t):
            if 'Bool'in t or 'U64'in t:return t
            if 'Binary'in t and t['Binary']['op']not in ('&&','||') and self.sort(t['Binary']['left'],env)=='U64' and words and not keep_arithmetic and arithmetic(t) and t['Binary']['left']!=t['Binary']['right']:
                pass
            elif 'Binary'in t and (words or t['Binary']['op']in ('&&','||') or self.sort(t['Binary']['left'],env)=='Bool' or t['Binary']['left']==t['Binary']['right']):return {'Binary':{**t['Binary'],**{k:abstract(t['Binary'][k])for k in ['left','right']}}}
            if 'If'in t:return {'If':{k:abstract(v)for k,v in t['If'].items()}}
            s=self.sort(t,env)
            if s not in ('Bool','U64'):raise ValueError('non-scalar abstraction')
            if t not in opaque:opaque.append(t);sorts.append(s)
            return var('scalar_'+str(opaque.index(t)))
        aa,zz=abstract(self.normal(a,env)),abstract(self.normal(z,env));conditions=[];premises=[]
        for l,r,p in facts:
            if self.sort(l,env)not in ('Bool','U64'):continue
            conditions.append(dict(**{'from':abstract(self.normal(l,env)),'to':abstract(self.normal(r,env))}));premises.append(p)
        if len(opaque)>64 or len(conditions)>32:raise ValueError('scalar authoring bound')
        params=[['scalar_'+str(i),s]for i,s in enumerate(sorts)]
        goal=dict(params=params,conditions=conditions,**{'from':aa,'to':zz})
        self.goal=goal
        key=json.dumps(goal,sort_keys=True,separators=(',',':'))
        if key in self.memo and self.memo[key] is None:raise ValueError('previous scalar counterexample')
        if key not in self.memo:
            cache=Path(__file__).resolve().parents[1]/'build/scalar-laws';cache.mkdir(parents=True,exist_ok=True)
            file=cache/(hashlib.sha256(key.encode()).hexdigest()+'.json')
            if file.exists():proof=json.loads(file.read_text())
            else:
                with tempfile.TemporaryDirectory(prefix='ink-scalar-')as d:
                    d=Path(d);(d/'goal.json').write_text(json.dumps(goal))
                    result=subprocess.run([str(self.compiler),'bitvector-obligation',str(d/'goal.json'),'-o',str(d/'cnf.json')],capture_output=True,text=True)
                    if result.returncode:raise ValueError(result.stderr)
                    try:cert=certificate(json.loads((d/'cnf.json').read_text()),seconds=10 if words else 2,conflicts=20000 if words else 2000)
                    except ValueError:
                        self.memo[key]=None;raise
                    proof={'BitVector':dict(**{'from':aa,'to':zz},hypotheses=list(range(len(conditions))),certificate=cert)}
                file.write_text(json.dumps(proof,separators=(',',':'))+'\n')
            self.memo[key]=self.add({'Theorem':dict(**goal,proof=proof)})
        return {'Use':dict(theorem=self.memo[key],arguments=opaque,premises=premises)}
