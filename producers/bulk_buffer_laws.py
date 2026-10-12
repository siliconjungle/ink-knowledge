#!/usr/bin/env python3
"""Checked bulk-buffer facts; algorithms and rewrite selection are untrusted."""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import value,var,term,word,op,law
CARRIERS=('U32','U64','I32','F32','Bool','String','Int','Unit')
def examples():
    result={};u=value('U32');zero=word('U32',0)
    for scalar in CARRIERS:
        a=value(scalar);seq=value({'List':scalar});buf=value({'Buffer':scalar})
        xs=var(seq,'xs');start=var(u,'start');count=var(u,'count');dest=var(u,'destination');v=var(a,'v')
        receiver=op(buf,'call:buffer',xs);prefix='bulk-buffer/'+scalar.lower()
        result[prefix+'/fill-zero']=law(dict(xs=seq,start=u,v=a),op(buf,'method:fill_range',receiver,start,zero,v),receiver)
        result[prefix+'/copy-zero']=law(dict(xs=seq,start=u,destination=u),op(buf,'method:copy_within',receiver,start,dest,zero),receiver)
        empty=op(buf,'call:buffer',term(seq,'Nil'))
        result[prefix+'/fill-empty']=law(dict(start=u,count=u,v=a),op(buf,'method:fill_range',empty,start,count,v),empty)
        result[prefix+'/copy-empty']=law(dict(start=u,destination=u,count=u),op(buf,'method:copy_within',empty,start,dest,count),empty)
        # Generalized list induction proves length preservation with arbitrary
        # offsets/counts, including zero, out-of-bounds and wrapping word values.
        def edited(xs,start,count):return op(seq,'local:fill-range',xs,start,count,v)
        def length(xs):return op(u,'call:length',xs)
        tail=var(seq,'tail')
        def branch(s,c):
            left=op(u,'binary:+',length(edited(tail,s,c)),word('U32',1))
            right=op(u,'binary:+',length(tail),word('U32',1))
            ih={'GeneralizedHypothesis':dict(index=0,arguments=dict(start=s,count=c,v=v))}
            return {'Trans':dict(middle=left,left='Normalize',right={'Trans':dict(middle=right,left={'Congruence':[ih,'Normalize']},right='Normalize')})}
        step={'Cases':dict(condition=op(value('Bool'),'binary:==',count,zero),on_true='Normalize',on_false={'Cases':dict(condition=op(value('Bool'),'binary:==',start,zero),on_true=branch(zero,op(u,'binary:-',count,word('U32',1))),on_false=branch(op(u,'binary:-',start,word('U32',1)),count))})}
        proof={'GeneralizedInduction':dict(variable='xs',generalize=['start','count','v'],names=['head','tail'],base='Normalize',step=step)}
        helper=law(dict(xs=seq,start=u,count=u,v=a),length(edited(xs,start,count)),length(xs),proof)
        result[prefix+'/fill-length-helper']=helper
        helper_id=identity(semantic_entry(helper))
        left=op(u,'method:len',op(buf,'method:fill_range',receiver,start,count,v))
        use={'Use':dict(law=helper_id,arguments=dict(xs=xs,start=start,count=count,v=v),premises=[])}
        public=law(helper['params'],left,length(xs),{'Trans':dict(middle=helper['from'],left='Normalize',right=use)})
        public['dependencies']=[helper_id];result[prefix+'/fill-length']=public
    return result

def publish(output):
    output=Path(output);previous=Store(output);objects=[]
    names=json.loads((output/'store/names.json').read_text());roots=json.loads((output/'store/rewrite-view.json').read_text())['roots'];entries=[]
    for name,proof in examples().items():
        obj=semantic_entry(proof);i=identity(obj);objects.append(obj);entries.append(i);names['rewrite/'+name]=i
        # Operational proof helpers cannot become source replacements.
        if not name.endswith('-helper'):roots.append(i)
    store=previous.extend(objects,names)
    (output/'store/rewrite-view.json').write_bytes(canonical(store.bundle(sorted(set(roots))))+b'\n')
    (output/'store/bulk-buffer-view.json').write_bytes(canonical(store.bundle(entries))+b'\n')
    store.rebuild()
    return store
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output-store',type=Path,required=True);a=parser.parse_args();s=publish(a.output_store);print(json.dumps(dict(laws=len(examples()),snapshot=s.snapshot_id)))
