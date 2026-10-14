"""Word-loop authoring must replay actual source preservation, not labels."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class SourceRepeatUntilObserver(unittest.TestCase):
    def test_preservation_fresh_names_and_changed_observer_rejection(self):
        root=Path(__file__).resolve().parents[2]
        compiler=Path(os.environ.get('INK_COMPILER',root/'target/debug/ink'))
        source='''module example;
record Cursor{data:List<u32>,index:u32,}
fn step(s:Cursor,amount:u32,loop_count:u32)->Cursor{
 return Cursor{data:s.data,index:s.index+amount+loop_count};
}
'''
        nested=source.replace('record Cursor{data:List<u32>,index:u32,}', 'record Inner{data:List<u32>,}\nrecord Cursor{inner:Inner,index:u32,}').replace('data:s.data','inner:s.inner')
        captured=source.replace('loop_count:u32)', 'loop_count:u32,__assumed_current:u32)').replace('s.index+amount+loop_count','s.index+amount+loop_count+__assumed_current')
        for name,text,accepted in [('preserved',source,True),('fresh-assumption',captured,True),('nested',nested,True),
                                   ('changed',source.replace('data:s.data','data:[]'),False),
                                   ('changed-branch',source.replace('data:s.data','data:choose(amount==0,s.data,[])'),False)]:
            with tempfile.TemporaryDirectory()as directory:
                d=Path(directory);src=d/'source.ink';src.write_text(text);core=d/'core.json'
                result=subprocess.run([compiler,'emit-core',src,'-o',core],capture_output=True,text=True,timeout=180)
                self.assertEqual(result.returncode,0,result.stderr[-2000:])
                command=[os.environ.get('INK_PYTHON','python3'),root/'tools/source_repeat_until_observer.py',
                         '--compiler',compiler,'--core',core,'--function','step','--state-parameter','s','--field','inner.data'if name=='nested'else'data',
                         '--generic-store',root/'knowledge/libraries/proofs/word-loop-frames',
                         '--generic-law','9b27674c60696026f68c3dc20cbc0ac64c86231f17287f39c71d16a204051567','-o',d/'proofs']
                result=subprocess.run(list(map(str,command)),capture_output=True,text=True,timeout=180)
                self.assertEqual(result.returncode==0,accepted,name+' '+result.stderr[-2500:])
                if accepted:
                    self.assertEqual(json.loads(result.stdout)['status'],'checked')
                    scope=json.loads((d/'proofs/scope.json').read_text())
                    self.assertEqual(scope['observer'],'inner.data'if name=='nested'else'data')


if __name__=='__main__':unittest.main()
