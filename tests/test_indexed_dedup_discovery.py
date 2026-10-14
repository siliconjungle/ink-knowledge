"""Normal recipe discovery, universal admission and independent ordered oracles."""
import copy,json,os,subprocess,tempfile,unittest
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from ink_knowledge.proposal_views import ProposalViews
from ink_knowledge.recipes import execute,load

ROOT=Path(__file__).resolve().parents[2]
COMPILER=Path(os.environ.get('INK_COMPILER',ROOT/'target/debug/ink')).resolve()

class IndexedDedupDiscovery(unittest.TestCase):
 def run_compiler(self,*args,success=True):
  r=subprocess.run(list(map(str,[COMPILER,*args])),capture_output=True,text=True,timeout=120)
  if success:self.assertEqual(r.returncode,0,r.stderr[-4000:])
  else:self.assertNotEqual(r.returncode,0)
  return r
 def proposals(self,d,source):
  (d/'input.ink').write_text(source);self.run_compiler('emit-core',d/'input.ink','-o',d/'core.json')
  core=json.loads((d/'core.json').read_text());source_id=json.loads(self.run_compiler('check-core',d/'core.json').stdout)['core_sha256']
  store=Store.publish(d/'knowledge',[]);registry,_=load(store=store)
  recipe=next(r for r in registry['recipes']if r['id']=='indexed-ordered-dedup')
  rows=list(execute(recipe,dict(core=core,source=source_id,compiler=str(COMPILER),knowledge_root=str(store.root),knowledge_snapshot=store.snapshot_id,check_timeout=120)))
  return rows,source_id,store
 def package(self,row,source):return dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=source,steps=row['steps'])
 def test_ordinary_loops_multiple_word_sorts_and_record_observers(self):
  sources=[
   ('frozen','U32',(ROOT/'bench/planning-corpus/heldout/compact-set.ink').read_text(),'run',True),
   ('renamed','U32','''module renamed;
record IndexedWords{other:u32,}
fn member(xs:List<u32>,needle:u32)->Bool{return false;}
fn saw(values:List<u32>,needle:u32)->Bool{return foldl(values,false,fn(value,found)=>found||value==needle);}
fn unique(values:List<u32>,__assumed_item:u32)->List<u32>{
 var result:List<u32>=[];for value in values {if !saw(result,value){result=result.concat([value]);}}return result;}
''','unique',True),
   ('wide','U64','''module wide;
fn unique(values:List<u64>)->List<u64>{return foldl(values,[],fn(value,output)=>
 choose(foldl(output,false,fn(item,found)=>found||value==item),output,output.concat([value])));}
''','unique',False),
   ('signed','I32','''module signed;
fn unique(values:List<i32>)->List<i32>{var output:List<i32>=[];for value in values {
 if !foldl(output,false,fn(item,found)=>found||item==value){output=output.concat([value]);}}return output;}
''','unique',False),
   ('record','U32','''module record_observer;
record Carrier{words:List<u32>,count:u32,}
fn unique(values:List<u32>)->List<u32>{return foldl(values,Carrier{words:[],count:0},fn(value,state)=>
 choose(foldr(state.words,false,fn(item,found)=>value==item||found),state,
 Carrier{words:state.words.concat([value]),count:state.count+1})).words;}
''','unique',False),
  ]
  for label,word,source,function,extra in sources:
   with self.subTest(label=label),tempfile.TemporaryDirectory()as temporary:
    d=Path(temporary);rows,source_id,store=self.proposals(d,source)
    proposals=[r for r in rows if r['status']=='proposal'];self.assertEqual(len(proposals),1,rows)
    package=self.package(proposals[0],source_id);(d/'plan.json').write_bytes(canonical(package))
    self.run_compiler('check-plan',d/'core.json',d/'plan.json','--core','--target','javascript')
    self.run_compiler('emit-plan',d/'core.json',d/'plan.json','--core','--target','javascript','-o',d/'selected.mjs')
    self.run_compiler('build',d/'core.json','--core','--target','javascript','-o',d/'baseline.mjs')
    samples={'U32':'[0,1,0xffffffff,17]','U64':'[0n,1n,0xffffffffffffffffn,9007199254740993n]','I32':'[-2147483648,-1,0,2147483647]'}[word]
    (d/'verify.mjs').write_text(f'''import assert from'node:assert/strict';import * as a from'./baseline.mjs';import * as b from'./selected.mjs';
const values={samples};
for(const n of [0,1,2,9,129])for(const reverse of [false,true]){{
 const xs=Array.from({{length:n}},(_,i)=>values[i%values.length]);if(reverse)xs.reverse();
 const before=xs.slice(),args=[xs{',17'if extra else ''}],expected=[...new Set(xs)];
 assert.deepEqual(a.call('{function}',args),expected);assert.deepEqual(b.call('{function}',args),expected);assert.deepEqual(xs,before);
}}
''')
    r=subprocess.run(['node',str(d/'verify.mjs')],capture_output=True,text=True,timeout=60);self.assertEqual(r.returncode,0,r.stderr)
    self.assertEqual(Store(store.root).snapshot_id,store.snapshot_id,'proposal must not mutate installed knowledge')
 def test_existing_accumulator_preserves_seed_duplicates_and_order(self):
  source='module seeded;\nfn unique(xs:List<u32>,seed:List<u32>)->List<u32>{return foldl(xs,seed,fn(item,output)=>choose(\n foldl(output,false,fn(key,found)=>found||item==key),output,output.concat([item])));}\n'
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);rows,source_id,_=self.proposals(d,source);row=next(r for r in rows if r['status']=='proposal')
   (d/'plan.json').write_bytes(canonical(self.package(row,source_id)))
   self.run_compiler('check-plan',d/'core.json',d/'plan.json','--core','--target','javascript')
   self.run_compiler('emit-plan',d/'core.json',d/'plan.json','--core','--target','javascript','-o',d/'selected.mjs')
   self.run_compiler('build',d/'core.json','--core','--target','javascript','-o',d/'baseline.mjs')
   (d/'verify.mjs').write_text("""import assert from'node:assert/strict';import * as a from'./baseline.mjs';import * as b from'./selected.mjs';
for(const seed of [[],[7,7,0],[0xffffffff,0,0xffffffff]])for(const xs of [[],[7,8,8,0,0xffffffff],[0,1,2,1]]){
 const beforeSeed=seed.slice(),before=xs.slice(),expected=seed.slice(),seen=new Set(seed);
 for(const x of xs)if(!seen.has(x)){seen.add(x);expected.push(x);}
 assert.deepEqual(a.call('unique',[xs,seed]),expected);assert.deepEqual(b.call('unique',[xs,seed]),expected);
 assert.deepEqual(seed,beforeSeed);assert.deepEqual(xs,before);
}
""")
   r=subprocess.run(['node',str(d/'verify.mjs')],capture_output=True,text=True,timeout=60);self.assertEqual(r.returncode,0,r.stderr)

 def test_structural_membership_inside_a_returned_record_preserves_other_fields(self):
  source='''module wrapped;
record Answer {words:List<u32>,stamp:u32,}
fn unique(xs:List<u32>,stamp:u32)->Answer {
 return Answer{words:foldl(xs,[],fn(item,output)=>choose(
  foldr(output,false,fn(key,found)=>[key]==[item]||found),output,output.concat([item]))),stamp:stamp};
}
'''
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);rows,source_id,_=self.proposals(d,source)
   proposals=[r for r in rows if r['status']=='proposal'];self.assertEqual(len(proposals),1,rows)
   (d/'plan.json').write_bytes(canonical(self.package(proposals[0],source_id)))
   self.run_compiler('check-plan',d/'core.json',d/'plan.json','--core','--target','javascript')
   self.run_compiler('emit-plan',d/'core.json',d/'plan.json','--core','--target','javascript','-o',d/'selected.mjs')
   self.run_compiler('build',d/'core.json','--core','--target','javascript','-o',d/'baseline.mjs')
   (d/'verify.mjs').write_text("""import assert from'node:assert/strict';import * as a from'./baseline.mjs';import * as b from'./selected.mjs';
for(const xs of [[],[0],[7,8,8,0,0xffffffff,7],[0,1,2,1]])for(const stamp of [0,19,0xffffffff]){
 const before=xs.slice(),expected={words:[...new Set(xs)],stamp};
 assert.deepEqual(a.call('unique',[xs,stamp]),expected);assert.deepEqual(b.call('unique',[xs,stamp]),expected);assert.deepEqual(xs,before);
}
""")
   r=subprocess.run(['node',str(d/'verify.mjs')],capture_output=True,text=True,timeout=60);self.assertEqual(r.returncode,0,r.stderr)

 def test_wrong_steps_and_forged_result_fail_closed(self):
  template='''module variants;
fn unique(xs:List<u32>)->List<u32>{return foldl(xs,SEED,fn(item,output)=>choose(
 foldl(output,false,fn(key,found)=>found||item==key),output,ADDITION));}
'''
  for label,source in [
   ('wrong_item',template.replace('SEED','[]').replace('ADDITION','output.concat([item+1])')),
   ('wrong_predicate',template.replace('SEED','[]').replace('ADDITION','output.concat([item])').replace('item==key','item!=key')),
  ]:
   with self.subTest(label=label),tempfile.TemporaryDirectory()as temporary:
    d=Path(temporary);rows,source,store=self.proposals(d,source)
    for i,row in enumerate(rows):
     if row['status']!='proposal':continue
     (d/'bad.json').write_bytes(canonical(self.package(row,source)))
     self.run_compiler('check-plan',d/'core.json',d/'bad.json','--core','--target','javascript',success=False)
  with tempfile.TemporaryDirectory()as temporary:
   d=Path(temporary);rows,source,store=self.proposals(d,template.replace('SEED','[]').replace('ADDITION','output.concat([item])'))
   row=next(r for r in rows if r['status']=='proposal');package=self.package(row,source)
   forged=copy.deepcopy(package);rewrite=forged['steps'][1]['package'];old=rewrite['applications'][0]['law']
   objects=copy.deepcopy(rewrite['knowledge']['objects']);obj=objects.pop(old)
   obj['payload']['to']={'sort':{'Value':{'List':'U32'}},'node':'Nil'};new=identity(obj);objects[new]=obj
   rewrite['knowledge']=ProposalViews(store,objects,d/'forged').bundle([new]);rewrite['applications'][0]['law']=new
   (d/'forged.json').write_bytes(canonical(forged));self.run_compiler('check-plan',d/'core.json',d/'forged.json','--core','--target','javascript',success=False)
if __name__=='__main__':unittest.main()
