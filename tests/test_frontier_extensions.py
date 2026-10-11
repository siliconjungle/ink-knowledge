"""Frozen authoring reproduction and authenticated false-mathematics controls."""
import gzip,hashlib,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT),str(ROOT/'producers')]
from freeze_frontier_extensions import candidates,bridge
from point_delta import free_variables
from test_column_layouts import wrong_bit

def read(directory,name):return json.loads(gzip.decompress((directory/(name+'.gz')).read_bytes()))

@unittest.skipUnless(os.environ.get('INK_COMPILER'),'requires explicit compiler')
class FrontierExtensions(unittest.TestCase):
    def test_archive_integrity_and_current_source_checked_reproduction(self):
        for directory in sorted((ROOT/'research/frontier-extensions-current').iterdir()):
            if not(directory/'manifest.json').exists():continue
            with self.subTest(case=directory.name),tempfile.TemporaryDirectory()as output:
                manifest=json.loads((directory/'manifest.json').read_text())
                for name,expected in manifest['files'].items():self.assertEqual(hashlib.sha256(gzip.decompress((directory/(name+'.gz')).read_bytes())).hexdigest(),expected)
                self.assertEqual(hashlib.sha256((directory/'source.ink').read_bytes()).hexdigest(),manifest['source_sha256'])
                # Historical packets bind the authoring implementation and
                # source model that produced them. Keep their exact hashes;
                # current producers must instead re-admit the current source.
                out=Path(output);compiler=os.environ['INK_COMPILER']
                def check(*args):
                    result=subprocess.run([compiler,*map(str,args)],capture_output=True,text=True)
                    self.assertEqual(result.returncode,0,result.stderr)
                check('emit-action-model',directory/'source.ink','-o',out/'model.json')
                generated=candidates(directory.name,json.loads((out/'model.json').read_text()),out/'database')
                self.assertEqual(len(generated),len(manifest['representations']))
                paths=[]
                for i,request in enumerate(generated):
                    path=out/(str(i)+'.json');path.write_text(json.dumps(request));paths.append(path)
                    check('check-representation',directory/'source.ink',path)
                for label,before,after in [('forward',0,1),('reverse',1,0)]:
                    request=bridge(generated[before],generated[after],out/(label+'-store'),True)
                    path=out/(label+'.json');path.write_text(json.dumps(request))
                    check('check-migration',directory/'source.ink',paths[before],paths[after],path)

    def reject(self,kind,index,mutator):
        directory=ROOT/'research/frontier-extensions-current'/kind
        request=read(directory,str(index)+'.json')
        with tempfile.TemporaryDirectory()as output:
            forged=wrong_bit(request,Path(output)/'store',mutator)
            path=Path(output)/'request.json';path.write_text(json.dumps(forged))
            result=subprocess.run([os.environ['INK_COMPILER'],'check-representation',directory/'source.ink',path],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertNotIn('source-definition closure mismatch',result.stderr)
            self.assertTrue(any(word in result.stderr for word in ['equality','proof','certificate']),result.stderr)

    def test_false_singleton_fold_is_rejected_by_mathematics(self):
        def change(body):
            if 'If'in body and free_variables(body)=={'aggregate_value'}:
                body['If']['on_false']={'U64':1};return True
            return False
        self.reject('fused',0,change)

    def test_false_ordered_contribution_is_rejected_by_mathematics(self):
        request=read(ROOT/'research/frontier-extensions-current/ordered','0.json')
        selected=next(e['payload']['declaration']['Function']for e in request['knowledge']['objects'].values()if 'Function'in e['payload'].get('declaration',{})and free_variables(e['payload']['declaration']['Function']['body'])=={'view_row'})
        original=selected['body'];result=selected['result']['Data']
        def change(body):
            if body!=original:return False
            body.clear();body.update({'Construct':dict(datatype=result,constructor=0,arguments=[])});return True
        self.reject('ordered',0,change)

    def test_false_dense_slot_is_rejected_by_mathematics(self):
        def change(body):
            if free_variables(body)!={'dense_base'} or 'Construct'not in body:return False
            fields=body['Construct']['arguments']
            if len(fields)<3 or 'Call'not in fields[1]:return False
            fields[1]['Call']['arguments'][1]={'U64':9};return True
        self.reject('dense',1,change)

    def test_false_bucket_filter_is_rejected_by_mathematics(self):
        def change(t):
            if isinstance(t,dict):
                x=t.get('Binary',{})
                if x.get('op')=='&'and x.get('right')=={'U64':1}:x['right']={'U64':2};return True
                return any(change(v)for v in t.values())
            if isinstance(t,list):return any(change(v)for v in t)
            return False
        self.reject('index',1,change)
if __name__=='__main__':unittest.main()
