"""Bounded tagged-word equations for private carriers and transport codecs.

This is an untrusted producer. The compiler reconstructs every bit-vector
obligation and replays the RUP proof. These equations do not certify JavaScript
emission, string parsing, dictionaries, ownership or whole-program lowering.
"""
import argparse,json,subprocess,tempfile
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from ink_knowledge.store import entry
from producers.bitvector_proofs import certificate
from producers.physical_capabilities import MATH

def word(n):return {'U64':n}
def var(n):return {'Var':n}
def op(kind,a,b):return {'Binary':dict(op=kind,left=a,right=b)}
def bound(x,n):return dict(**{'from':op('<=',x,word(n)),'to':{'Bool':True}})

def goals(bits):
    if not 1<=bits<=12:raise ValueError('tag width must be 1..12')
    payload,tag=var('payload'),var('tag');radix=1<<bits;low=radix-1;high=((1<<64)-1)^low
    encoded=op('+',op('*',payload,word(radix)),tag)
    params=[['payload','U64'],['tag','U64']]
    conditions=[bound(payload,(1<<(53-bits))-1),bound(tag,low)]
    common=dict(params=params,conditions=conditions)
    return {
      'tag':dict(**common,**{'from':op('&',encoded,word(low)),'to':tag}),
      'payload':dict(**common,**{'from':op('&',encoded,word(high)),'to':op('*',payload,word(radix))}),
      'exact53':dict(**common,**{'from':op('<=',encoded,word((1<<53)-1)),'to':{'Bool':True}}),
      'remove-tag':dict(**common,**{'from':op('-',encoded,tag),'to':op('*',payload,word(radix))}),
    }

def produce(compiler,destination,widths=range(1,13)):
    compiler=Path(compiler).resolve();objects=[];names={}
    with tempfile.TemporaryDirectory(prefix='ink-tagged-word-') as scratch:
        scratch=Path(scratch)
        for bits in widths:
            for name,goal in goals(bits).items():
                path=scratch/'goal.json';cnf=scratch/'cnf.json';path.write_bytes(canonical(goal)+b'\n')
                subprocess.run([str(compiler),'bitvector-obligation',str(path),'-o',str(cnf),'--circuit','shared-v2'],check=True,capture_output=True,text=True,timeout=30)
                proof=certificate(json.loads(cnf.read_bytes()),seconds=5,conflicts=20000);proof['encoding']='shared-v2'
                theorem=dict(**goal,proof={'BitVector':dict(**{'from':goal['from'],'to':goal['to']},hypotheses=list(range(len(goal['conditions']))),certificate=proof)})
                obj=entry('theorem',MATH,{'declaration':{'Theorem':theorem}},parameters=dict(goal['params']),conditions=goal['conditions'])
                objects.append(obj);names[f'value-layout/tagged-word/{bits}/{name}']=identity(obj)
    store=Store.publish(destination,objects,names)
    view=store.bundle(sorted(names.values()));path=Path(destination)/'tagged-word-view.json';path.write_bytes(canonical(view)+b'\n')
    with tempfile.TemporaryDirectory(prefix='ink-tagged-word-check-') as temp:
        temp=Path(temp);source=temp/'context.ink';core=temp/'context.json'
        source.write_text('module tag_word_context; fn identity(value: u64) -> u64 { return value; }\n')
        subprocess.run([str(compiler),'emit-core',str(source),'-o',str(core)],check=True,capture_output=True,text=True,timeout=30)
        checked=subprocess.run([str(compiler),'knowledge-check',str(core),str(path)],capture_output=True,text=True,timeout=120)
        if checked.returncode:raise ValueError(checked.stderr.strip())
    return store,names

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--compiler',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--bits',type=int,action='append');a=p.parse_args()
    store,names=produce(a.compiler,a.output,a.bits or range(1,13));print(json.dumps(dict(snapshot=store.snapshot_id,equations=len(names),view=str(a.output/'tagged-word-view.json'))))
if __name__=='__main__':main()
