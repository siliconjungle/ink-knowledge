"""Generic composition uses checked dependencies, never source-name authority."""
import copy,json,os,subprocess,tempfile,unittest,sys
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'tools'))
from source_field_preservation import author as preserve
class Composition(unittest.TestCase):
 def test_renamed_records_false_dependency_and_missing_condition(self):
  compiler=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'));python=os.environ.get('INK_PYTHON',sys.executable)
  source='''module generic;
record State{values:List<u32>,count:u32,}
fn helper(q:State)->State{return State{values:q.values,count:q.count+1};}
fn outer(s:State,yes:Bool)->State{let next=helper(s);return choose(yes,next,State{values:next.values,count:0});}
'''
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);src=d/'source.ink';src.write_text(source);core=d/'core.json';subject=d/'subject.json'
   for args in [('emit-core',src,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
    r=subprocess.run(list(map(str,[compiler,*args])),capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1500:])
   obj,lid=preserve(json.loads(core.read_text()),json.loads(subject.read_text()),'helper','q',['values'])
   false=copy.deepcopy(obj);theorem=dict(false['payload'],schema=1,semantics=false['semantics'],dependencies=false['dependencies']);theorem['to']={'sort':theorem['to']['sort'],'node':'Nil'};false=semantic_entry(theorem)
   conditional=copy.deepcopy(obj);theorem=dict(conditional['payload'],schema=1,semantics=conditional['semantics'],dependencies=conditional['dependencies']);theorem['conditions']=[{'from':{'sort':{'Value':'Bool'},'node':{'Bool':False}},'to':{'sort':{'Value':'Bool'},'node':{'Bool':True}}}];conditional=semantic_entry(theorem)
   for label,dependency,accepted in [('valid',obj,True),('false',false,False),('conditional',conditional,False)]:
    store=Store.publish(d/label,[dependency]);out=d/(label+'-result');r=subprocess.run(list(map(str,[python,ROOT/'tools/source_field_composition.py','--compiler',compiler,'--core',core,'--dependency-store',store.root,'--function','outer','--state-parameter','s','--field','values','-o',out])),capture_output=True,text=True,timeout=120)
    self.assertEqual(r.returncode==0,accepted,label+' '+r.stderr[-1800:]);self.assertEqual(out.exists(),accepted)

 def test_nested_projection_skips_unrelated_record_work(self):
  compiler=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
  source='module nested;record Inner{values:List<u32>,} record State{inner:Inner,count:u32,} fn outer(s:State,yes:Bool)->State{return choose(yes,State{inner:s.inner,count:s.count+1},State{inner:s.inner,count:0});}'
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);src=d/'source.ink';src.write_text(source);core=d/'core.json'
   r=subprocess.run([compiler,'emit-core',src,'-o',core],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
   dependency=Store.publish(d/'empty',[]);r=subprocess.run(list(map(str,[sys.executable,ROOT/'tools/source_field_composition.py','--compiler',compiler,'--core',core,'--dependency-store',dependency.root,'--function','outer','--state-parameter','s','--field','inner.values','-o',d/'result'])),capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1500:]);self.assertEqual(json.loads(r.stdout)['status'],'checked')


 def test_inline_callback_conversion_uses_fresh_binders(self):
  compiler=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
  source='module callbacks;record State{values:List<u32>,count:u32,} fn wrapper(s:State)->State{return State{values:s.values,count:s.count+1};} fn original(s:State,__congruence:u32)->State{return repeat_until(__congruence,s,fn(s)=>false,fn(i)=>fn(s)=>State{values:s.values,count:s.count+1});}'
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);src=d/'source.ink';src.write_text(source);core=d/'core.json'
   r=subprocess.run([compiler,'emit-core',src,'-o',core],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
   r=subprocess.run(list(map(str,[sys.executable,ROOT/'tools/source_repeat_until_observer.py','--compiler',compiler,'--core',core,'--function','wrapper','--state-parameter','s','--field','values','--generic-store',ROOT/'knowledge/libraries/proofs/word-loop-frames','--generic-law','9b27674c60696026f68c3dc20cbc0ac64c86231f17287f39c71d16a204051567','-o',d/'dependency'])),capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1500:])
   r=subprocess.run(list(map(str,[sys.executable,ROOT/'tools/source_field_composition.py','--compiler',compiler,'--core',core,'--dependency-store',d/'dependency','--function','original','--state-parameter','s','--field','values','--unfold','wrapper','-o',d/'result'])),capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1500:]);self.assertEqual(json.loads(r.stdout)['status'],'checked')


 def test_beta_substitution_traverses_list_literals(self):
  from source_field_preservation import substitute,shift,beta
  word=lambda node:{'sort':{'Value':'U32'},'node':node}
  list_sort={'Value':{'List':'U32'}}
  bound=word({'Bound':0});nil={'sort':list_sort,'node':'Nil'}
  cons={'sort':list_sort,'node':{'Cons':[bound,nil]}}
  argument=word({'Word':7})
  expected={'sort':list_sort,'node':{'Cons':[argument,nil]}}
  self.assertEqual(substitute(cons,argument),expected)
  self.assertEqual(shift(cons,1)['node']['Cons'][0]['node'],{'Bound':1})
  function={'sort':{'Arrow':[{'Value':'U32'},list_sort]},'node':{'Lambda':cons}}
  application={'sort':list_sort,'node':{'Op':['apply',[function,argument]]}}
  self.assertEqual(beta(application,[100]),expected)
  nested={'sort':list_sort,'node':{'Cons':[{'sort':{'Value':'U32'},'node':{'Op':['apply',[{'sort':{'Arrow':[{'Value':'U32'},{'Value':'U32'}]},'node':{'Lambda':bound}},argument]]}},nil]}}
  self.assertEqual(beta(nested,[100]),expected)


 def test_list_literal_inside_source_beta_is_checked(self):
  compiler=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
  source='module list_beta;record State{values:List<u32>,count:u32,} fn outer(s:State,yes:Bool)->State{let values=s.values;let rows=[s.count];return choose(yes,s,State{values:values,count:rows.at_or(0,0)});}'
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);src=d/'source.ink';src.write_text(source);core=d/'core.json'
   result=subprocess.run([compiler,'emit-core',src,'-o',core],capture_output=True,text=True,timeout=120);self.assertEqual(result.returncode,0,result.stderr)
   dependency=Store.publish(d/'empty',[])
   result=subprocess.run(list(map(str,[sys.executable,ROOT/'tools/source_field_composition.py','--compiler',compiler,'--core',core,'--dependency-store',dependency.root,'--function','outer','--state-parameter','s','--field','values','-o',d/'result'])),capture_output=True,text=True,timeout=120)
   self.assertEqual(result.returncode,0,result.stderr[-1500:]);self.assertEqual(json.loads(result.stdout)['status'],'checked')


 def test_explicit_equation_endpoints_replay_and_false_goal_rejects(self):
  compiler=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
  source='module equations;record State{values:List<u32>,count:u32,} fn outer(s:State)->State{return State{values:s.values,count:s.count+1};}'
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);src=d/'source.ink';src.write_text(source);core=d/'core.json'
   r=subprocess.run([compiler,'emit-core',src,'-o',core],capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
   state={'Value':{'Named':'State'}};word={'Value':'U32'};s={'sort':state,'node':{'Free':'s'}}
   start={'sort':word,'node':{'Op':['field:count',[{'sort':state,'node':{'Op':['call:outer',[s]]}}]]}}
   target={'sort':word,'node':{'Op':['binary:+',[{'sort':word,'node':{'Op':['field:count',[s]]}},{'sort':word,'node':{'Word':1}}]]}}
   dependency=Store.publish(d/'empty',[])
   for label,to,accepted in [('valid',target,True),('false',{'sort':word,'node':{'Word':0}},False)]:
    equation=d/(label+'.json');equation.write_text(json.dumps({'params':{'s':state},'from':start,'to':to}))
    r=subprocess.run(list(map(str,[sys.executable,ROOT/'tools/source_field_composition.py','--compiler',compiler,'--core',core,'--dependency-store',dependency.root,'--function','outer','--state-parameter','s','--field','count','--equation',equation,'-o',d/label])),capture_output=True,text=True,timeout=120)
    self.assertEqual(r.returncode==0,accepted,r.stderr[-1500:]);self.assertEqual((d/label).exists(),accepted)


 def test_dependency_reduction_under_callback_uses_opened_binders(self):
  compiler=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
  source='module callbacks;record State{values:List<u32>,count:u32,} fn changed(s:State)->State{return State{values:s.values,count:s.count+1};} fn before(xs:List<State>)->List<List<u32>>{return xs.map(fn(s)=>s.values);} fn after(xs:List<State>)->List<List<u32>>{return xs.map(fn(s)=>changed(s).values);}'
  with tempfile.TemporaryDirectory()as temp:
   d=Path(temp);src=d/'source.ink';src.write_text(source);core=d/'core.json';subject=d/'subject.json'
   for args in [('emit-core',src,'-o',core),('emit-semantic',core,'--core','-o',subject)]:
    r=subprocess.run(list(map(str,[compiler,*args])),capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr)
   obj,lid=preserve(json.loads(core.read_text()),json.loads(subject.read_text()),'changed','s',['values']);dependency=Store.publish(d/'dependencies',[obj])
   xs_sort={'Value':{'List':{'Named':'State'}}};result={'Value':{'List':{'List':'U32'}}};xs={'sort':xs_sort,'node':{'Free':'xs'}}
   equation=d/'equation.json';equation.write_text(json.dumps({'params':{'xs':xs_sort},'from':{'sort':result,'node':{'Op':['call:before',[xs]]}},'to':{'sort':result,'node':{'Op':['call:after',[xs]]}}}))
   r=subprocess.run(list(map(str,[sys.executable,ROOT/'tools/source_field_composition.py','--compiler',compiler,'--core',core,'--dependency-store',dependency.root,'--function','before','--state-parameter','xs','--field','unused','--unfold','after','--equation',equation,'-o',d/'result'])),capture_output=True,text=True,timeout=120);self.assertEqual(r.returncode,0,r.stderr[-1800:])
   names=json.loads((d/'result/store/names.json').read_text());result_store=Store(d/'result');proof=result_store.object(names['source/composed_field']);self.assertIn(lid,proof['dependencies'])

if __name__=='__main__':unittest.main()
