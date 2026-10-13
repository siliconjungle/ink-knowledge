"""Propose a word-sum basis for a bounded modular sum, with ordinary proofs.

The maintained carrier uses the full word group. Its public observation applies
the source mask. This avoids assuming that every arbitrary summary word already
lies in the bounded range. The kernel checks both the scalar and induction laws.
"""
import hashlib,json,subprocess,tempfile
from pathlib import Path
from producers.action_replacement import var,call,cons,convert,trans
from producers.point_delta import binary,sub,lift
from producers.bitvector_proofs import certificate

def lift_sum(query,objects,add,compiler,cache):
    if 'Call' not in query:return None
    node=query['Call'];original=node['function']
    fn=objects[original]['payload']['declaration'].get('Function')
    if not fn or fn['result']!='U64' or fn['recursive']!=0 or len(fn['params'])!=1:return None
    body=fn['body'].get('Match')
    if not body or body['scrutinee']!=var(fn['params'][0][0]) or len(body['branches'])!=2:return None
    empty,step=body['branches']
    if empty!=dict(bindings=[],body={'U64':0}) or len(step['bindings'])!=2:return None
    masked=step['body'].get('Binary',{});mask=masked.get('right',{}).get('U64')
    if masked.get('op')!='&' or type(mask)is not int or not 0<mask<(1<<64) or mask&(mask+1):return None
    head,tail=step['bindings'];addition=binary('+',var(head),{'SelfCall':[var(tail)]})
    if masked.get('left')!=addition:return None
    sequence=fn['params'][0][1]
    if not isinstance(sequence,dict) or 'Data'not in sequence:return None
    datatype=objects[sequence['Data']]['payload']['declaration'].get('Datatype')
    if not datatype or [c['fields']for c in datatype['constructors']]!=[[],['U64','SelfType']]:return None
    projected=lambda value:binary('&',value,{'U64':mask})
    h,t=var('modular_head'),var('modular_tail')
    left,right=projected(binary('+',h,projected(t))),projected(binary('+',h,t))
    goal=dict(params=[['modular_head','U64'],['modular_tail','U64']],conditions=[],**{'from':left,'to':right})
    digest=hashlib.sha256(json.dumps(goal,sort_keys=True).encode()).hexdigest();file=Path(cache)/(digest+'.json')
    if file.exists():proof=json.loads(file.read_text())
    else:
        with tempfile.TemporaryDirectory(prefix='ink-modular-law-')as directory:
            path=Path(directory);(path/'goal.json').write_text(json.dumps(goal))
            result=subprocess.run([str(compiler),'bitvector-obligation',str(path/'goal.json'),'-o',str(path/'cnf.json')],capture_output=True,text=True)
            if result.returncode:raise ValueError(result.stderr)
            cert=certificate(json.loads((path/'cnf.json').read_text()))
            if len(cert['steps'])>20000:raise ValueError('modular sum scalar proof step bound')
            proof={'BitVector':dict(**{'from':left,'to':right},hypotheses=[],certificate=cert)}
        file.parent.mkdir(parents=True,exist_ok=True);file.write_text(json.dumps(proof,separators=(',',':'))+'\n')
    scalar=add({'Theorem':dict(**goal,proof=proof)})
    basis=add({'Function':{**fn,'body':{'Match':{**body,'branches':[empty,{**step,'body':addition}]}}}})
    xs=var('modular_items');nil=cons(sequence['Data'],0,[]);hd=cons(sequence['Data'],1,[h,t])
    original_sum=lambda x:call(original,[x]);basis_sum=lambda x:call(basis,[x])
    a,z=original_sum(xs),projected(basis_sum(xs))
    ih={'Hypothesis':0}
    congruence={'Binary':dict(op='&',left={'Binary':dict(op='+',left={'Refl':h},right=ih)},right={'Refl':{'U64':mask}})}
    step_proof=trans(convert(original_sum(hd),projected(binary('+',h,original_sum(t)))),congruence,
        {'Use':dict(theorem=scalar,arguments=[h,basis_sum(t)],premises=[])},convert(projected(binary('+',h,basis_sum(t))),projected(basis_sum(hd))))
    fusion=add({'Theorem':dict(params=[['modular_items',sequence]],conditions=[],**{'from':a,'to':z},proof={'Induction':dict(variable='modular_items',**{'from':a,'to':z},cases=[dict(bindings=[],proof=convert(original_sum(nil),projected(basis_sum(nil)))),dict(bindings=['modular_head','modular_tail'],proof=step_proof)])})})
    return dict(term=call(basis,node['arguments']),mask=mask,
        proof={'Use':dict(theorem=fusion,arguments=node['arguments'],premises=[])})
