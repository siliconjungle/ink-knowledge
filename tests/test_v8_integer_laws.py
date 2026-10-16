"""Exact signed/unsigned refinements retain source work and lazy defaults."""
import copy,json,os,random,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.frozen_laws import read
from producers.v8_integer_laws import templates
from producers.semantic_laws import value,var,word,op,term
ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'knowledge/producers/data/v8-integer-laws'
SOURCE=Path(__file__).parent/'fixtures/v8-integer/source.ink'
FUNCTIONS=dict(strict_zero='i32_quot_or_zero_divisor',strict_self='i32_quot_or_self',lazy_default='i32_quot_or_minus_one',signed_quot='i32_quot_or_power_3',signed_rem='i32_rem_or_power_3',negative_quot='i32_quot_or_power_negative_3',negative_rem='i32_rem_or_power_negative_3',minus_quot='i32_quot_or_minus_one',minus_rem='i32_rem_or_minus_one',minimum_quot='i32_quot_or_minimum_divisor',minimum_rem='i32_rem_or_minimum_divisor',sign_fill='i32_sign_fill',unsigned_quot='u32_quot_or_power_3',unsigned_rem='u32_rem_or_power_3',wide_quot='u64_quot_or_power_3',wide_rem='u64_rem_or_power_3')
def compiler():return Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()
def run(*args,ok=True):
 r=subprocess.run(list(map(str,args)),capture_output=True,text=True,timeout=120)
 if ok and r.returncode:raise AssertionError(r.stderr[-4000:])
 return r

def packet(directory):
 from ink_planner.semantic_search import positions,match
 d=Path(directory);d.mkdir(parents=True,exist_ok=True)
 run(compiler(),'emit-core',SOURCE,'-o',d/'core.json');run(compiler(),'emit-semantic',d/'core.json','--core','-o',d/'semantic.json')
 subject=json.loads((d/'semantic.json').read_bytes());rows={r['name']:r['law']for r in read(DATA)}
 objects={name:semantic_entry(rows[name])for name in set(FUNCTIONS.values())}
 store=Store.publish(d/'knowledge',objects.values());applications=[]
 for function,name in FUNCTIONS.items():
  law=rows[name]
  for path,target in positions(subject['functions'][function]):
   args={}
   if match(law['from'],target,law['params'],args):
    applications.append(dict(function=function,path=list(path),law=identity(objects[name]),arguments=args,premises=[]));break
  else:raise AssertionError('missing law '+function)
 result=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=store.bundle(sorted({a['law']for a in applications})),applications=applications)
 (d/'selection.json').write_bytes(canonical(result));run(compiler(),'check-selection',d/'core.json',d/'selection.json');return result

class IntegerLaws(unittest.TestCase):
 def test_independent_integer_oracle_checks_every_template_and_strict_trace(self):
  class Poison(Exception):pass
  def evaluate(t,env,trace,bound=()):
   n=t['node'];kind=t['sort'].get('Value')if isinstance(t['sort'],dict)else None
   mask=(1<<(64 if kind=='U64'else 32))-1
   if 'Free'in n:
    name=n['Free'];trace.append(name);v=env[name]
    if v is None:raise Poison()
    return v
   if 'Bound'in n:return bound[-1-n['Bound']]
   if 'Word'in n:return n['Word']
   if 'Bool'in n:return n['Bool']
   if 'Lambda'in n:return lambda a:evaluate(n['Lambda'],env,trace,(*bound,a))
   name,args=n['Op']
   if name=='call:choose':return evaluate(args[1]if evaluate(args[0],env,trace,bound)else args[2],env,trace,bound)
   a=evaluate(args[0],env,trace,bound)
   if name=='apply':return a(evaluate(args[1],env,trace,bound))
   if name=='neg':return (-a)&mask
   b=evaluate(args[1],env,trace,bound)
   signed=lambda v:v-(1<<32)if v&(1<<31)else v
   if name in ['call:quot_or','call:rem_or']:
    x,y=(signed(a),signed(b))if kind=='I32'else(a,b)
    if y==0 or kind=='I32'and x==-(1<<31)and y==-1:return evaluate(args[2],env,trace,bound)
    q=(abs(x)//abs(y))*(-1 if (x<0)!=(y<0)else 1)
    return (q if name=='call:quot_or'else x-q*y)&mask
   if name=='call:word_and':return (a&b)&mask
   if name=='call:word_or':return (a|b)&mask
   if name=='call:wrapping_shl':return (a<<(b&(63 if kind=='U64'else 31)))&mask
   if name=='call:wrapping_shr':return ((signed(a)if kind=='I32'else a)>>(b&(63 if kind=='U64'else 31)))&mask
   if name in ['binary:+','binary:*']:return ((a+b)if name=='binary:+'else(a*b))&mask
   if name.startswith('binary:'):
    if args[0]['sort']==value('I32'):a,b=signed(a),signed(b)
    return {'==':lambda:a==b,'<':lambda:a<b}[name[7:]]()
   raise AssertionError(name)
  rng=random.Random(0x7838696e74)
  for row in templates():
   width=64 if any(s==value('U64')for s in row['goal']['params'].values())else 32;mask=(1<<width)-1
   values=[0,1,7,8,mask,1<<(width-1),(1<<(width-1))-1,mask-7]+[rng.getrandbits(width)for _ in range(12)]
   for i,x in enumerate(values):
    for poisoned in [False,True]:
     env={name:(x if name=='x'else values[(i+3)%len(values)]if name=='y'else None if poisoned else values[(i+5)%len(values)])for name in row['goal']['params']}
     outcomes=[]
     for end in ['from','to']:
      trace=[]
      try:answer=evaluate(row['goal'][end],env,trace)
      except Poison:answer='poisoned lazy fallback'
      outcomes.append((answer,trace))
     self.assertEqual(*outcomes,(row['name'],x,poisoned))

 def test_frozen_laws_replay_and_rehashed_invalid_signed_rewrite_rejects(self):
  goals={r['name']:r['goal']for r in templates()}
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);run(compiler(),'emit-core',SOURCE,'-o',d/'core.json')
   def check(law):
    with tempfile.TemporaryDirectory(dir=d)as candidate:
     obj=semantic_entry(law);store=Store.publish(candidate,[obj]);(d/'bundle.json').write_bytes(canonical(store.bundle([identity(obj)])))
     return run(compiler(),'knowledge-check',d/'core.json',d/'bundle.json',ok=False)
   rows=read(DATA)
   for row in rows:
    self.assertEqual({k:row['law'][k]for k in ['params','conditions','from','to']},goals[row['name']]);self.assertEqual(check(row['law']).returncode,0,row['name'])
   original=copy.deepcopy(next(r['law']for r in rows if r['name']=='i32_quot_or_minus_one'))
   for mode in ['opaque-v1','fixed-words-v2','fixed-scalars-v3']:
    bad=copy.deepcopy(original);bad['proof']['BitVector']['semantics']=mode;self.assertNotEqual(check(bad).returncode,0)
   bad=copy.deepcopy(original);bad['to']=op(value('I32'),'neg',var(value('I32'),'x'))
   (d/'false.json').write_bytes(canonical({k:bad[k]for k in ['params','conditions','from','to']}))
   run(compiler(),'semantic-bitvector-obligation',d/'core.json',d/'false.json','--core','--semantics','fixed-scalars-v4','--encoding','shared-v2','-o',d/'cnf.json')
   bad['proof']['BitVector']['certificate']['problem_sha256']=json.loads((d/'cnf.json').read_bytes())['sha256']
   self.assertNotEqual(check(bad).returncode,0)

 def test_catalog_discovery_matches_renamed_operands_without_function_names(self):
  from producers.v8_integer_laws import specialize
  catalog=json.loads((ROOT/'knowledge/ink_knowledge/producer-catalog.json').read_bytes())
  self.assertIn('producers.v8_integer_laws',catalog['modules'])
  self.assertEqual(specialize({'functions':{}},{}),[])
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);source=d/'source.ink'
   source.write_text('module unrelated_name;fn arbitrary(payload:u64,backup:u64)->u64{return quot_or(payload,8,backup);}')
   run(compiler(),'emit-core',source,'-o',d/'core.json');run(compiler(),'emit-semantic',d/'core.json','--core','-o',d/'subject.json')
   found=dict(specialize(json.loads((d/'subject.json').read_bytes()),{}))
   self.assertIn('v8-integer/u64_quot_or_power_3',found)
   self.assertNotIn('v8-integer/u64_quot_or_power_4',found)

 def test_wide_self_quotient_is_discovered_and_keeps_strict_work_and_lazy_fallback(self):
  from ink_planner.semantic_search import positions,match
  from producers.v8_integer_laws import specialize
  row=next(row for row in read(DATA)if row['name']=='u64_quot_or_self');law=row['law'];obj=semantic_entry(law)
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);run(compiler(),'emit-core',SOURCE,'-o',d/'core.json')
   run(compiler(),'emit-semantic',d/'core.json','--core','-o',d/'semantic.json');subject=json.loads((d/'semantic.json').read_bytes())
   self.assertTrue(any(name=='v8-integer/u64_quot_or_self'for name,_ in specialize({'functions':{'renamed':subject['functions']['wide_self']}},{})))
   store=Store.publish(d/'knowledge',[obj]);applications=[]
   for function in ['strict_wide_self','wide_self']:
    for path,target in positions(subject['functions'][function]):
     arguments={}
     if match(law['from'],target,law['params'],arguments):
      applications.append(dict(function=function,path=list(path),law=identity(obj),arguments=arguments,premises=[]));break
    else:self.fail('missing wide self application')
   selection=dict(schema=1,semantics='ink-evidence-v1',input_core_sha256=subject['input_core_sha256'],knowledge=store.bundle([identity(obj)]),applications=applications)
   (d/'selection.json').write_bytes(canonical(selection));run(compiler(),'check-selection',d/'core.json',d/'selection.json')
   def call(function,args,budget=100000,selected=False):
    (d/'args.json').write_bytes(canonical(args))
    return run(compiler(),'run',d/'core.json',function,d/'args.json','--core','--evaluation-budget',budget,*(['--selection',d/'selection.json']if selected else []),ok=False)
   values=[0,1,(1<<64)-1,(1<<63),(1<<53)+1]
   for bits in [8,16,24,32,40,48,56]:values.extend([(1<<bits)-1,1<<bits,(1<<bits)+1])
   fallback=(1<<63)+17
   self.assertEqual(call('once_wide',[9],1500).returncode,0)
   for selected in [False,True]:
    self.assertNotEqual(call('strict_wide_self',[9],1500,selected).returncode,0)
    self.assertEqual(json.loads(call('strict_wide_self',[9],2500,selected).stdout),1)
    self.assertNotEqual(call('strict_wide_self',[0],2500,selected).returncode,0)
    self.assertEqual(json.loads(call('strict_wide_self',[0],100000,selected).stdout),73)
    self.assertEqual(json.loads(call('wide_self',[values,fallback],100000,selected).stdout),[fallback if x==0 else 1 for x in values])

 def test_source_applications_keep_unused_and_repeated_work_and_lazy_fallback(self):
  with tempfile.TemporaryDirectory()as tmp:
   d=Path(tmp);selection=packet(d);self.assertEqual(len(selection['applications']),len(FUNCTIONS))
   def call(name,value,budget,selected=False):
    (d/'args.json').write_bytes(canonical([value]));return run(compiler(),'run',d/'core.json',name,d/'args.json','--core','--evaluation-budget',budget,*(['--selection',d/'selection.json']if selected else []),ok=False)
   for selected in [False,True]:
    self.assertNotEqual(call('strict_zero',9,100,selected).returncode,0)
    self.assertEqual(json.loads(call('strict_zero',9,100000,selected).stdout),5)
    self.assertEqual(json.loads(call('lazy_default',9,100,selected).stdout),-9)
    self.assertNotEqual(call('lazy_default',-(1<<31),100,selected).returncode,0)
    self.assertEqual(json.loads(call('lazy_default',-(1<<31),100000,selected).stdout),7)
   self.assertEqual(call('once',9,1500).returncode,0)
   self.assertNotEqual(call('strict_self',9,1500).returncode,0)
   self.assertNotEqual(call('strict_self',9,1500,True).returncode,0)
   for selected in [False,True]:self.assertEqual(json.loads(call('strict_self',9,100000,selected).stdout),1)

if __name__=='__main__':
 import sys
 if len(sys.argv)>1:packet(sys.argv[1])
 else:unittest.main()
