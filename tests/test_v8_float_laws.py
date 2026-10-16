"""Exact IEEE source proofs preserve bit identity, scope and strict inputs."""
import copy,json,math,os,random,struct,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.frozen_laws import read
from producers.v8_float_laws import templates
from producers.semantic_laws import value,var,word,op,term

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'knowledge/producers/data/v8-float-laws'
SOURCE=Path(__file__).parent/'fixtures/v8-f32/source.ink'
FUNCTIONS=dict(roundtrip='float_bits_roundtrip',raw_roundtrip='word_bits_roundtrip',twice='double_negation',nan_neg='nan_negation',finite_neg='finite_negation',neg_bits='negated_bits',neg_raw='negated_from_bits',nan_raw='nan_from_bits',finite_raw='finite_from_bits',self_eq='self_equal',self_ne='self_unequal',self_lt='self_less',self_gt='self_greater',self_le='self_le',self_ge='self_ge',copied='float_bits_roundtrip',classes='nan_negation',observed='self_less')
def compiler():return Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()
def run(*args,ok=True):
 r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=120)
 if ok and r.returncode:raise AssertionError(r.stderr[-4000:])
 return r

def packet(directory):
 from ink_planner.semantic_search import match,positions
 d=Path(directory);d.mkdir(parents=True,exist_ok=True);core=d/'core.json';subject=d/'semantic.json'
 run(compiler(),'emit-core',SOURCE,'-o',core)
 run(compiler(),'emit-semantic',core,'--core','-o',subject)
 model=json.loads(subject.read_bytes());rows={r['name']:r['law']for r in read(DATA)}
 objects={name:semantic_entry(law)for name,law in rows.items()};store=Store.publish(d/'knowledge',objects.values());apps=[]
 for function,name in FUNCTIONS.items():
  law=rows[name]
  for path,target in positions(model['functions'][function]):
   bindings={}
   if match(law['from'],target,law['params'],bindings):
    apps.append(dict(function=function,path=list(path),law=identity(objects[name]),arguments=bindings,premises=[]));break
  else:raise AssertionError('missing pattern '+function)
 result=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=model['input_core_sha256'],knowledge=store.bundle(sorted({a['law']for a in apps})),applications=apps)
 path=d/'selection.json';path.write_bytes(canonical(result));run(compiler(),'check-selection',core,path)
 return result

class FloatLaws(unittest.TestCase):
 def test_independent_ieee_values_include_payloads_signed_zero_and_subnormals(self):
  def f(n):return struct.unpack('<f',struct.pack('<I',n))[0]
  def evaluate(t,env,bound=()):
   n=t['node'];kind=t['sort']
   if 'Free'in n:return env[n['Free']]
   if 'Bound'in n:return bound[-1-n['Bound']]
   for name in ['Float','Word','Bool']:
    if name in n:return n[name]
   if 'Lambda'in n:return lambda x:evaluate(n['Lambda'],env,(*bound,x))
   name,args=n['Op'];a=[evaluate(x,env,bound)for x in args]
   if name=='apply':return a[0](a[1])
   if name=='neg':return a[0]^0x80000000
   if name in ['call:f32_bits','call:f32_from_bits']:return a[0]
   if name in ['call:is_nan','call:is_finite']:return (math.isnan if name=='call:is_nan'else math.isfinite)(f(a[0]))
   if name=='call:word_xor':return a[0]^a[1]
   if name=='call:word_and':return a[0]&a[1]
   if name.startswith('binary:'):
    if args[0]['sort']==value('F32'):a=list(map(f,a))
    return {'==':lambda:a[0]==a[1],'!=':lambda:a[0]!=a[1],'<':lambda:a[0]<a[1],'>':lambda:a[0]>a[1],'<=':lambda:a[0]<=a[1],'>=':lambda:a[0]>=a[1]}[name[7:]]()
   raise AssertionError(name)
  rng=random.Random(0x783832);values=[0,0x80000000,1,0x80000001,0x007fffff,0x00800000,0x7f7fffff,0xff7fffff,0x7f800000,0xff800000,0x7f800001,0xff800001,0x7fc01234,0xffc04321,0xffffffff]+[rng.getrandbits(32)for _ in range(96)]
  rows=templates();self.assertEqual(len(rows),15)
  for row in rows:
   for raw in values:
    self.assertEqual(evaluate(row['goal']['from'],dict(x=raw,raw=raw)),evaluate(row['goal']['to'],dict(x=raw,raw=raw)),(row['name'],hex(raw)))

 def test_frozen_proofs_legacy_mode_substitution_and_false_rehashed_goal(self):
  goals={r['name']:r['goal']for r in templates()};rows=read(DATA);self.assertEqual(len(rows),15)
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);run(compiler(),'emit-core',SOURCE,'-o',d/'core.json')
   def check(objects,label):
    store=Store.publish(d/label,objects);path=d/(label+'.json');path.write_bytes(canonical(store.bundle([identity(o)for o in objects])))
    return run(compiler(),'knowledge-check',d/'core.json',path,ok=False)
   objects=[]
   for row in rows:
    self.assertEqual({k:row['law'][k]for k in ['params','conditions','from','to']},goals[row['name']]);objects.append(semantic_entry(row['law']))
   self.assertEqual(check(objects,'all').returncode,0)
   law=copy.deepcopy(next(r['law']for r in rows if r['name']=='float_bits_roundtrip'))
   for mode in ['opaque-v1','fixed-words-v2']:
    bad=copy.deepcopy(law);bad['proof']['BitVector']['semantics']=mode
    self.assertNotEqual(check([semantic_entry(bad)],mode).returncode,0)
   bad=copy.deepcopy(next(r['law']for r in rows if r['name']=='self_equal'));bad['to']=term(value('Bool'),{'Bool':True})
   request=d/'bad-goal.json';request.write_bytes(canonical({k:bad[k]for k in ['params','conditions','from','to']}));cnf=d/'bad-cnf.json'
   run(compiler(),'semantic-bitvector-obligation',d/'core.json',request,'--core','--semantics','fixed-scalars-v3','--encoding','shared-v2','-o',cnf)
   bad['proof']['BitVector']['certificate']['problem_sha256']=json.loads(cnf.read_bytes())['sha256']
   self.assertNotEqual(check([semantic_entry(bad)],'false-self-equality').returncode,0)

 def test_source_bound_applications_under_callbacks_and_strict_false(self):
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);selected=packet(d);self.assertEqual(len(selected['applications']),18)
   # Low fuel distinguishes retained operand execution from unsafe erasure.
   args=d/'args.json';args.write_text('[1]')
   for extra in [[],['--selection',d/'selection.json']]:
    result=run(compiler(),'run',d/'core.json','observed',args,'--core',*extra,'--evaluation-budget','100',ok=False)
    self.assertNotEqual(result.returncode,0,'strict operand was dropped')
    self.assertIn('budget',result.stderr)
    result=run(compiler(),'run',d/'core.json','observed',args,'--core',*extra,'--evaluation-budget','100000')
    self.assertEqual(json.loads(result.stdout),False)

if __name__=='__main__':
 import sys
 if len(sys.argv)==2:packet(Path(sys.argv[1]))
 else:unittest.main()
