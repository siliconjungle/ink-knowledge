import json,os,subprocess,tempfile,unittest
from pathlib import Path
from producers.early_return import candidates
from producers.cell_actions import candidates as cell_candidates

COMPILER=Path(os.environ.get('INK_COMPILER','target/debug/ink')).resolve()
ROOT=Path(__file__).resolve().parents[1]
PREFIX='''module early_returns;enum Error{Missing,Cancelled,}state Values:Table<u64,u64> = Table.empty();event changed:u64;
'''
@unittest.skipUnless(COMPILER.is_file(),'requires Ink compiler')
class EarlyReturnTests(unittest.TestCase):
    def proposals(self,source,directory,producer=candidates):
        d=Path(directory);(d/'source.ink').write_text(source)
        for command,out in [('emit-core','core.json'),('emit-action-model','model.json')]:
            emitted=subprocess.run([str(COMPILER),command,str(d/'source.ink'),'-o',str(d/out)],capture_output=True,text=True)
            self.assertEqual(emitted.returncode,0,emitted.stderr)
        return list(producer(dict(core=json.loads((d/'core.json').read_bytes()),model=json.loads((d/'model.json').read_bytes()),compiler=str(COMPILER),knowledge_root=str(ROOT))))
    def check(self,row,directory):
        p=row['steps'][0]['package'];d=Path(directory)
        (d/'plan.json').write_text(json.dumps(dict(schema=1,semantics='ink-compiled-plan-v1',input_core_sha256=p['input_core_sha256'],steps=row['steps'])))
        return subprocess.run([str(COMPILER),'check-plan',str(d/'source.ink'),str(d/'plan.json')],capture_output=True,text=True)
    def test_success_and_failure_observations_authorize_early_return(self):
        source=PREFIX+'''change write(k:u64,v:u64,cancel:Bool)->Result<Unit,Error> writes(Values) emits(changed){Values.put(k,v);emit changed(v);if cancel{return Err(Error.Cancelled);}return Ok(());}'''
        with tempfile.TemporaryDirectory()as d:
            rows=self.proposals(source,d);row=next(r for r in rows if r['status']=='proposal')
            checked=self.check(row,d);self.assertEqual(checked.returncode,0,checked.stderr)
            # Changing the proposed early return invalidates the complete proof.
            selected=row['steps'][0]['package']['action_replacement']['selected']
            selected['program']['actions'][0]['body'][0]['If'][1][0]['Return']={'Call':['Ok',['Unit']]}
            self.assertNotEqual(self.check(row,d).returncode,0)
    def test_an_earlier_failure_cannot_be_hidden(self):
        source=PREFIX+'''change write(k:u64,v:u64,cancel:Bool)->Result<Unit,Error> reads(Values) writes(Values){let old:u64=Values.get(k).ok_or(Error.Missing)?;Values.put(k,v);if cancel{return Err(Error.Cancelled);}return Ok(());}'''
        with tempfile.TemporaryDirectory()as d:
            rows=self.proposals(source,d);self.assertTrue(rows)
            for row in rows:
                if row['status']=='proposal':self.assertNotEqual(self.check(row,d).returncode,0)
    def test_local_dependency_is_not_moved_out_of_scope(self):
        source=PREFIX+'''change write(k:u64,v:u64,cancel:Bool)->Result<Unit,Error> writes(Values){let stop:Bool=cancel;Values.put(k,v);if stop{return Err(Error.Cancelled);}return Ok(());}'''
        with tempfile.TemporaryDirectory()as d:self.assertEqual(self.proposals(source,d),[])
    def test_single_upsert_preserves_unmodified_filtered_queries(self):
        source='''module price_cells;record Price{cost:u64,live:Bool,}state Prices:Table<u64,Price> = Table.empty();
keep total:u64=sum(Prices.values().filter(fn(p)=>p.live).map(fn(p)=>p.cost));
keep size:u64=sum(Prices.values().filter(fn(p)=>p.live).map(fn(p)=>p.cost*0+1));
change write(k:u64,p:Price)->Unit writes(Prices){if Prices.contains(k){Prices.replace(k,p);}else{Prices.insert(k,p);}return ();}
query total_query()->u64 reads(total){return total;}query size_query()->u64 reads(size){return size;}'''
        with tempfile.TemporaryDirectory()as d:
            row=next(r for r in self.proposals(source,d,cell_candidates)if r['status']=='proposal')
            checked=self.check(row,d);self.assertEqual(checked.returncode,0,checked.stderr)
            objects=row['steps'][0]['package']['knowledge']['objects']
            self.assertTrue(any(any(n.startswith('bridge_arg')for n,_ in o['payload'].get('declaration',{}).get('Theorem',{}).get('params',[]))for o in objects.values()))
    def test_effectful_key_cannot_acquire_a_presence_fact(self):
        # The source checker already rejects a changing key under contains:
        # the second evaluation cannot inherit the first key's presence fact.
        source='module changing_keys;state Values:Table<u64,u64> = Table.empty();state Ticks:Table<u64,u64> = Table.empty();\nchange next_key()->u64 reads(Ticks) writes(Ticks){let k:u64=Ticks.get(0).unwrap_or(0);Ticks.put(0,k+1);return k;}\nchange write(v:u64)->Unit reads(Ticks) writes(Values,Ticks){if Values.contains(next_key()){Values.replace(next_key(),v);}else{Values.insert(next_key(),v);}return ();}'
        with tempfile.TemporaryDirectory()as d:
            source_path=Path(d)/'source.ink';source_path.write_text(source)
            checked=subprocess.run([str(COMPILER),'check',str(source_path)],capture_output=True,text=True)
            self.assertNotEqual(checked.returncode,0);self.assertIn('needs proof that the key is present',checked.stderr)
