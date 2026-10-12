"""Physical reservations authored from ordinary, source-bound cardinality proofs."""
import copy
from producers.planning_recipes import row
from producers.semantic_laws import value,var,op,term

def propose(context):
    if context.get('representation'):return
    signatures={f['name']:f for f in context['core']['program']['functions']}
    for packet in context.get('properties',[]):
        for fact in packet['facts']:
            f=signatures[fact['function']]
            if not isinstance(f['result'],dict) or 'List' not in f['result']:continue
            count=lambda v:op(value('Int'),'call:count',v)
            node=fact['context'].get('node',{}).get('Op')
            if not node or node[0]!='binary:<=' or len(node[1])!=2:continue
            right=node[1][1].get('node',{}).get('Op')
            if not right or right[0]!='call:count' or len(right[1])!=1:continue
            capacity=right[1][0];place=capacity;fields=[]
            while 'Op' in place['node']:
                operation,args=place['node']['Op']
                if not operation.startswith('field:') or len(args)!=1:break
                fields.append(operation[6:]);place=args[0]
            name=place['node'].get('Free')
            if name not in dict(f['params']):continue
            fields.reverse()
            expected=op(value('Bool'),'binary:<=',count(var(value(f['result']),fact['subject_variable'])),count(capacity))
            if fact['context']!=expected or fact['value']!=term(value('Bool'),{'Bool':True}):continue
            plan=copy.deepcopy(context.get('physical')or dict(schema=1,semantics='ink-physical-plan-v1',input_core_sha256=context['source'],tables='ordered',definitions='shared',borrow_reads=[],borrow_rows=[],packed_datatypes=[],memo_functions=[]))
            evidence=dict(packet,facts=[fact]);reservations=[r for r in plan.get('reservations',[]) if r['function']!=f['name']]
            plan['reservations']=[*reservations,dict(function=f['name'],parameter=name,fields=fields,evidence=evidence)]
            yield row('physical',plan,'proved result capacity/'+f['name']+'/'+name+'.'+'.'.join(fields))
