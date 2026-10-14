"""Author reusable value-parametric map laws using the general map equality rule.

This generator supplies proof data only. It neither installs entries nor makes
optimisation or profitability decisions; emit-laws must check every certificate.
"""
import json
from pathlib import Path
from producers.semantic_laws import value,var,op

def documents():
    source=['module ink.knowledge.map_algebra;'];evidence={}
    for key_type,spelling in [('Bool','Bool'),('U32','u32'),('U64','u64'),('I32','i32')]:
        k=value(key_type);q=var(k,'map_key');a=var(k,'a');b=var(k,'b')
        split={'Cases':dict(condition=op(value('Bool'),'binary:==',q,a),on_true='Normalize',on_false='Normalize')}
        def add(name,params,left,right,proof,requires=''):
            name='map_'+name+'_'+key_type.lower()
            source.append(f'law {name}<V>({params}) {{\n {requires}\n {left}=={right};\n proof by provided;\n}}')
            evidence[name]=dict(proof={'MapExtensional':dict(parameter='map_key',fallback_parameter='map_fallback',presence=proof,values=proof)})
        m=f'm:Map<{spelling},V>,a:{spelling}'
        add('overwrite',m+',x:V,y:V','m.set(a,x).set(a,y)','m.set(a,y)',split)
        add('remove_twice',m,'m.remove(a).remove(a)','m.remove(a)',split)
        add('remove_after_set',m+',x:V','m.set(a,x).remove(a)','m.remove(a)',split)
        split_b={'Cases':dict(condition=op(value('Bool'),'binary:==',q,b),on_true='Normalize',on_false='Normalize')}
        both={'Cases':dict(condition=op(value('Bool'),'binary:==',q,a),on_true=split_b,on_false=split_b)}
        add('same_value_updates',m+f',b:{spelling},x:V','m.set(a,x).set(b,x)','m.set(b,x).set(a,x)',both)
        if key_type!='Bool':
            order={'Order':dict(atoms=[q,a,b],body='Normalize')}
            add('distinct_updates',m+f',b:{spelling},x:V,y:V','m.set(a,x).set(b,y)','m.set(b,y).set(a,x)',order,'requires distinct: a!=b;')
    return '\n\n'.join(source)+'\n',evidence

def write(directory):
    directory=Path(directory);directory.mkdir(parents=True,exist_ok=True)
    source,evidence=documents();(directory/'map-algebra.ink').write_text(source)
    (directory/'map-algebra.proofs.json').write_text(json.dumps(evidence,indent=2)+'\n')
    return directory/'map-algebra.ink',directory/'map-algebra.proofs.json'

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('output');args=parser.parse_args();write(args.output)
