import json,os,tempfile,unittest
from pathlib import Path
from producers.maintained_folds import produce
ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink'))
class DatabaseGroups(unittest.TestCase):
 def source(self,where,operation='!='):
  p=where/'source.ink';p.write_text('''module unfamiliar;
record Item{flag:Bool,other:Bool,}
state Values:Table<u64,Item>=Table.empty();
fn folded(xs:List<Item>)->Bool{return foldr(xs,false,fn(e)=>fn(acc)=>(e.flag&&e.other)OPacc);}
keep answer:Bool=folded(Values.values());
change put(k:u64,v:Item)->Unit writes(Values){Values.put(k,v);return ();}
change remove(k:u64)->Unit writes(Values){Values.remove(k);return ();}
query read()->Bool reads(answer){return answer;}
'''.replace('OP',operation));return p
 def test_different_boolean_formula_is_admitted_without_a_new_compiler_rule(self):
  with tempfile.TemporaryDirectory()as tmp:
   p=Path(tmp);source=self.source(p)
   # Same group, different total definition: no recognised operator name grants authority.
   spec=dict(result='Bool',zero={'Bool':False},combine={'If':{'condition':{'Var':'a'},'on_true':{'Binary':{'op':'==','left':{'Var':'b'},'right':{'Bool':False}}},'on_false':{'Var':'b'}}},inverse={'Var':'a'})
   plan=produce(source,COMPILER,p/'authored',groups=[spec]);self.assertEqual(len(plan['steps'][0]['package']['views']),1)
 def test_or_cannot_be_used_as_an_invertible_group(self):
  with tempfile.TemporaryDirectory()as tmp:
   p=Path(tmp);source=self.source(p,'||')
   spec=dict(result='Bool',zero={'Bool':False},combine={'Binary':{'op':'||','left':{'Var':'a'},'right':{'Var':'b'}}},inverse={'Var':'a'})
   with self.assertRaisesRegex(ValueError,'no factorised folds'):produce(source,COMPILER,p/'authored',groups=[spec])
 def test_wrong_source_reduction_does_not_acquire_parity_maintenance(self):
  with tempfile.TemporaryDirectory()as tmp:
   p=Path(tmp);source=self.source(p,'||')
   with self.assertRaisesRegex(ValueError,'no factorised folds'):produce(source,COMPILER,p/'authored')
if __name__=='__main__':unittest.main()
