"""Guarded parameter specialization uses ordinary universal representation proofs."""
import copy,hashlib,json,os,subprocess,tempfile,unittest
from pathlib import Path
from producers.representations import generate
from ink_knowledge import Store,identity,canonical
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'tests/fixtures/parameter-cache/source.ink'


def reauthenticate(request,objects,directory):
    renamed,rebuilt,pending={},{},dict(objects)
    def rewrite(v):
        if isinstance(v,str):
            if v.startswith('call:'):return 'call:'+renamed.get(v[5:],v[5:])
            return renamed.get(v,v)
        if isinstance(v,dict):return {k:rewrite(x)for k,x in v.items()}
        if isinstance(v,list):return [rewrite(x)for x in v]
        return v
    while pending:
        ready=[k for k,e in pending.items()if not any(d in pending for d in e['dependencies'])]
        assert ready
        for old in ready:
            e=rewrite(pending.pop(old));e['dependencies']=sorted(set(e['dependencies']))
            e['interface']['operations']=sorted(set(e['interface']['operations']))
            new=identity(e);renamed[old]=new;rebuilt[new]=e
    rid=renamed[request['representation']]
    return dict(request,representation=rid,knowledge=Store.publish(directory,rebuilt.values()).bundle([rid]))


@unittest.skipUnless(os.environ.get('INK_COMPILER'),'requires explicit compiler')
class ParameterCacheTests(unittest.TestCase):
    def invoke(self,*args):
        return subprocess.run([os.environ['INK_COMPILER'],*map(str,args)],capture_output=True,text=True,timeout=120)
    def model(self,p):
        result=self.invoke('emit-action-model',SOURCE,'-o',p/'model.json')
        self.assertEqual(result.returncode,0,result.stderr)
        return json.loads((p/'model.json').read_text())
    def check(self,p,request,success=True):
        path=p/'request.json';path.write_text(json.dumps(request))
        result=self.invoke('check-representation',SOURCE,path)
        if success:self.assertEqual(result.returncode,0,result.stderr)
        else:self.assertNotEqual(result.returncode,0)
        return result
    def test_one_two_and_four_exact_arguments_are_universally_checked(self):
        with tempfile.TemporaryDirectory()as tmp:
            p=Path(tmp);model=self.model(p)
            for query,args in [('get',[2**64-1]),('score',[7,True]),('four',[0,False,2**64-1,True])]:
                with self.subTest(query=query):
                    result=generate(model,p/query,cache_query=query,preserve_cache=True,cache_arguments=args)
                    for request in result['requests']:self.check(p,request)
                    (p/'migration.json').write_text(json.dumps(result['migration']))
                    for i,request in enumerate(result['requests']):(p/(str(i)+'.json')).write_text(json.dumps(request))
                    check=self.invoke('check-migration',SOURCE,p/'0.json',p/'1.json',p/'migration.json')
                    self.assertEqual(check.returncode,0,check.stderr)
    def test_invalid_or_unbounded_arguments_decline(self):
        with tempfile.TemporaryDirectory()as tmp:
            p=Path(tmp);model=self.model(p)
            for query,args in [('get',[]),('get',[True]),('get',[-1]),('get',[2**64]),('get',[1,2]),('score',[7,1]),('zero',[]),('get',{'x':7})]:
                with self.subTest(query=query,args=args),self.assertRaises(ValueError):
                    generate(model,p/'invalid',cache_query=query,preserve_cache=True,cache_arguments=args)
            for options in [dict(compact_queries=True),dict(dynamic_delta=True),dict(preserve_cache=False)]:
                with self.assertRaises(ValueError):
                    generate(model,p/'invalid',cache_query='get',cache_arguments=[0],**{'preserve_cache':True,**options})
    def test_default_cache_packet_is_unchanged(self):
        with tempfile.TemporaryDirectory()as tmp:
            p=Path(tmp);model=self.model(p)
            a=generate(model,p/'a',cache_query='zero',preserve_cache=True)
            b=generate(model,p/'b',cache_query='zero',preserve_cache=True,cache_arguments=None)
            self.assertEqual(a,b)
            # Frozen from the pre-specialization producer at 243f1bfb.
            self.assertEqual(hashlib.sha256(canonical(a)).hexdigest(),
                '898aa485428efa5a332579436496ccc473a19bf24ebcb45b8260d9d1263bf847')
            self.check(p,a['requests'][1])
    def test_discovery_is_bounded_and_every_tuple_is_checked(self):
        from producers.parameter_cache import candidates
        from producers.planning_recipes import parameter_cache
        with tempfile.TemporaryDirectory()as tmp:
            p=Path(tmp);model=self.model(p)
            hints=list(candidates(model))
            self.assertEqual(len(hints),4)
            self.assertTrue(all(name in model['actions'] and 1<=len(args)<=4 for name,args in hints))
            rows=list(parameter_cache(dict(model=model,compiler=os.environ['INK_COMPILER'])))
            self.assertEqual(len(rows),len(hints))
            self.assertTrue(all(r['status']=='proposal'for r in rows),str(rows)[:1000])
            for row in rows:self.check(p,row['step']['package'])
    def test_rehashed_wrong_guard_cannot_reuse_a_different_argument(self):
        with tempfile.TemporaryDirectory()as tmp:
            p=Path(tmp);model=self.model(p)
            request=generate(model,p/'good',cache_query='get',preserve_cache=True,cache_arguments=[7])['requests'][1]
            objects=copy.deepcopy(request['knowledge']['objects']);changed=0
            def mutate(node):
                nonlocal changed
                if isinstance(node,dict):
                    if 'If'in node and node['If']['condition']=={'Binary':dict(op='==',left={'Var':'arg_0'},right={'U64':7})}:
                        node['If']['condition']['Binary']['right']={'U64':8};changed+=1
                    for child in node.values():mutate(child)
                elif isinstance(node,list):
                    for child in node:mutate(child)
            for e in objects.values():
                f=e['payload'].get('declaration',{}).get('Function')
                if f:mutate(f['body'])
            self.assertEqual(changed,1)
            forged=reauthenticate(request,objects,p/'forged')
            result=self.check(p,forged,False)
            self.assertIn('equality',result.stderr)

if __name__=='__main__':unittest.main()
