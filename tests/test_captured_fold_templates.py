"""Source templates preserve captures through ordinary extension and proof replay."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from ink_knowledge.source_algorithms import propose
from producers.captured_fold_batching import templates

ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
NEGATIVE='''
pub fn varying_inputs(groups:List<List<u32>>)->List<u32> {
 return groups.map(fn(xs)=>foldl(xs,0,fn(item,acc)=>acc+item));
}
pub fn filtered_inputs(xs:List<u32>,seeds:List<u32>)->List<u32> {
 return seeds.map(fn(seed)=>foldl(xs.filter(fn(x)=>x!=seed),seed,fn(item,acc)=>acc+item));
}
'''

class CapturedFolds(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.temporary=tempfile.TemporaryDirectory();d=Path(cls.temporary.name);cls.directory=d
  cls.source=d/'source.ink';cls.source.write_text((ROOT/'knowledge/libraries/examples/independent-fold-batching.ink').read_text()+NEGATIVE)
  def run(*args):
   r=subprocess.run([str(COMPILER),*map(str,args)],capture_output=True,text=True,timeout=120)
   if r.returncode:raise AssertionError(r.stderr)
   return json.loads(r.stdout)
  cls.source_id=run('emit-core',cls.source,'-o',d/'core.json')['core_sha256'];cls.core=json.loads((d/'core.json').read_text())
  names=run('emit-laws',ROOT/'knowledge/libraries/independent-fold-batching.ink','-o',d/'laws.json')['names']
  bundle=json.loads((d/'laws.json').read_text());cls.rule=names['map_fusion'];rows=templates(cls.rule)
  cls.store=Store.publish(d/'knowledge',[*bundle['objects'].values(),rows[0]['object']])
  context=dict(core=cls.core,compiler=str(COMPILER),source=cls.source_id,knowledge_root=str(cls.store.root),knowledge_snapshot=cls.store.snapshot_id,check_timeout=120)
  cls.candidates=list(propose(context))
 @classmethod
 def tearDownClass(cls):cls.temporary.cleanup()
 def check(self,steps,label):
  path=self.directory/(label+'.plan.json');path.write_bytes(canonical(dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=self.source_id,steps=steps)))
  return subprocess.run([str(COMPILER),'check-plan',str(self.source),str(path),'--target','javascript'],capture_output=True,text=True,timeout=120)
 def test_ordinary_templates_discover_captures_and_exclude_variable_inputs(self):
  found=set()
  for i,candidate in enumerate(self.candidates):
   self.assertEqual(candidate['status'],'proposal',candidate)
   self.assertEqual([s['kind']for s in candidate['steps']],['extension','rewrite'])
   application=candidate['steps'][-1]['package']['applications'][0];found.add(application['function'])
   r=self.check(candidate['steps'],'valid-'+str(i));self.assertEqual(r.returncode,0,r.stderr)
  self.assertEqual(found,{'captured_seed','words','floating','columns'})
 def test_rehashed_change_to_retained_environment_is_rejected(self):
  candidate=copy.deepcopy(next(c for c in self.candidates if c['steps'][-1]['package']['applications'][0]['function']=='captured_seed'))
  package=candidate['steps'][-1]['package'];view=package['knowledge'];root=package['applications'][0]['law'];original=view['objects'][root]
  payload=copy.deepcopy(original['payload'])
  # Replace the retained environment in the physical update with its evolving
  # state, keeping well-typed terms and regenerating every content identity.
  changes=0
  def corrupt(term):
   nonlocal changes
   if isinstance(term,dict):
    node=term.get('node',{});op=node.get('Op')if isinstance(node,dict)else None
    if op and op[0]=='field:environment':op[0]='field:state';changes+=1
    for v in term.values():corrupt(v)
   elif isinstance(term,list):
    for v in term:corrupt(v)
  corrupt(payload['to']);self.assertGreater(changes,0)
  forged=semantic_entry(dict(schema=1,semantics=original['semantics'],dependencies=original['dependencies'],**payload));ident=identity(forged)
  entries={**view['objects'],ident:forged};store=Store.publish(self.directory/'forged',entries.values())
  package['knowledge']=store.bundle([ident]);package['applications'][0]['law']=ident
  r=self.check(candidate['steps'],'forged-capture');self.assertNotEqual(r.returncode,0,r.stdout)
 def test_shared_adapter_does_not_discharge_conditions(self):
  from ink_knowledge.higher_patterns import adapter
  row=templates(self.rule)[0]['object']['payload']['law'];conditional=copy.deepcopy(row)
  conditional['conditions']=[{'from':row['from'],'to':row['to']}]
  adapted=adapter('0'*64,conditional,row['from'])
  self.assertIsNotNone(adapted)
  # Matching higher-order holes may eta-expand their arguments. The
  # instantiated obligation must remain explicit in the derived law.
  self.assertEqual(len(adapted['conditions']),len(conditional['conditions']))
  self.assertIn("'Hypothesis': 0",repr(adapted['proof']))
  self.assertEqual(adapted['dependencies'],['0'*64])
 def test_normal_search_admits_capture_conversion_without_forcing_a_winner(self):
  import sys
  d=self.directory/'normal-search';d.mkdir()
  result=subprocess.run([sys.executable,'-m','ink_planner.compiled_planning',
   '--compiler',str(COMPILER),'--source',str(self.source),'--knowledge-root',str(self.store.root),
   '--target','javascript','--planning-effort','quick','--measurement-mode','off','--cache','off',
   '--time-seconds','60','--keep-candidates',str(d/'candidates'),'-o',str(d/'plan.json')],
   cwd=ROOT,capture_output=True,text=True,timeout=120)
  self.assertEqual(result.returncode,0,result.stderr)
  self.assertEqual(json.loads((d/'plan.json').read_text())['steps'],[])
  found=[]
  for path in (d/'candidates').glob('*.plan.json'):
   plan=json.loads(path.read_text())
   if any(s['kind']=='extension'for s in plan['steps'])and any(s['kind']=='rewrite'and any(a['function']=='captured_seed'for a in s['package']['applications'])for s in plan['steps']):found.append(path.name)
  self.assertTrue(found,'normal search must reach the source-template adapter')

if __name__=='__main__':unittest.main()
