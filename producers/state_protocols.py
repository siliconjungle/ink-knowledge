"""Whole state implementations selected as data, independently checked by Ink.

This producer composes protocol/read/publication choices with scalar-column codec
proofs. Shapes, capacities and integer lanes are alternatives, never profile facts.
"""
import copy,json,tempfile,subprocess,gzip
from pathlib import Path
from ink_knowledge import Store,canonical,identity
from .physical_capabilities import invoke,write,codec_objects,bit_proof

def base(source):
    return dict(schema=1,semantics='ink-state-protocol-v1',input_core_sha256=source,actions=[],direct_reads=[],output_publication=False,snapshot_rows=False,event_columns=False,inline_maintenance=False,columns=[])

def column_codec(context,record,exact,directory):
    source=write(directory/'core.json',context['core']);out=directory/'schema.json'
    invoke(context['compiler'],'emit-column-codec',source,'--core','--entry',record,'-o',out)
    schema=json.loads(out.read_bytes());objects,roundtrip=codec_objects(schema);guards={}
    if exact:
        v={'Var':'value'};binary=lambda op,a,b:{'Binary':dict(op=op,left=a,right=b)}
        for field,t in schema['fields']:
            if t!='U64':continue
            mask={'U64':(1<<53)-1}
            goal=dict(params=[['value','U64']],conditions=[dict(**{'from':binary('<=',v,mask),'to':{'Bool':True}})],**{'from':binary('&',v,mask),'to':v})
            guards[field]=bit_proof(context['compiler'],directory,goal)
    store=Store.publish(directory/'codec-store',objects)
    return dict(record=record,roundtrip=roundtrip,packing={},knowledge=store.bundle([roundtrip])),guards

def candidates(context,capacities=(256,4096),integer_lanes=(False,True)):
    if context.get('representation')or context.get('emit_target')!='javascript':
        yield dict(status='declined',label='state-protocols',reason='requires JavaScript source state');return
    current=copy.deepcopy(context.get('protocol')or base(context['source']))
    program=context['core']['program'];facts=context.get('protocol_capabilities',[])
    explicit=program.get('contracts',{}).get('action_protocols',{})
    actions=[dict(action=f['action'],execution='preflight')for f in facts if f['preflight']and explicit.get(f['action'])!='transactional']
    maintained=set((context.get('maintained')or{}).get('keeps',[]))
    keeps=program['keeps']
    reads=[f['action']for f in facts if f['direct_keep']is not None and keeps[f['direct_keep']]['name']in maintained]
    alternatives=[]
    if maintained:
        p=copy.deepcopy(current);p['inline_maintenance']=not current.get('inline_maintenance',False);alternatives.append(('inline-maintenance',p))
    if program.get('events')or program['states']:
        p=copy.deepcopy(current)
        if current.get('compact_commits'):p.pop('compact_commits')
        else:p['compact_commits']=json.loads(gzip.decompress(Path(__file__).with_name('data').joinpath('commit-word53.json.gz').read_bytes()))
        alternatives.append(('compact-commits',p))
    if program.get('events'):
        p=copy.deepcopy(current);p['event_columns']=not current.get('event_columns',False);alternatives.append(('event-columns',p))
    if program['states']:
        p=copy.deepcopy(current);p['snapshot_rows']=not current.get('snapshot_rows',False);alternatives.append(('snapshot-row-cache',p))
    if actions:
        p=copy.deepcopy(current);p['actions']=actions;alternatives.append(('preflight',p))
    if reads:
        p=copy.deepcopy(current);p['direct_reads']=reads;p['output_publication']=True;alternatives.append(('direct-publication',p))
    if actions and reads:
        p=copy.deepcopy(current);p.update(actions=actions,direct_reads=reads,output_publication=True);alternatives.append(('fused-protocol',p))
    blocked={c['table']for c in current['columns']}|{c['table']for c in (context.get('physical')or{}).get('dense_prefixes',[])}
    records=program['records'];cache={}
    with tempfile.TemporaryDirectory(prefix='ink-state-protocols-')as temporary:
        directory=Path(temporary)
        for root in program['states']:
            t=root['ty'];table=t.get('Table')if isinstance(t,dict)else None
            if root['name']in blocked or not table or table[0]not in ['U64','U32']:continue
            record=table[1].get('Named')if isinstance(table[1],dict)else None
            if record not in records or not records[record]or not all(t in ['U64','U32','I32','F32','Bool']for _,t in records[record]):continue
            for exact in integer_lanes:
                try:
                    key=(record,exact)
                    if key not in cache:
                        path=directory/(record+str(exact));path.mkdir();cache[key]=column_codec(context,record,exact,path)
                    for capacity in capacities:
                        p=copy.deepcopy(current);p['columns'].append(dict(table=root['name'],capacity=capacity,exact_numbers=exact,codec=cache[key][0],guards=cache[key][1]));p['columns'].sort(key=lambda c:c['table'])
                        alternatives.append((f'columns/{root["name"]}/{capacity}/{"exact-number"if exact else"word64"}',p))
                except (ValueError,OSError,ImportError,subprocess.TimeoutExpired)as e:yield dict(status='declined',label='column-codec',reason=str(e)[-2000:])
    seen={identity(current)}
    for label,p in alternatives:
        key=identity(p)
        if key in seen:continue
        seen.add(key)
        yield dict(status='proposal',label='state-protocols/'+label,step=dict(kind='protocol',package=p))
