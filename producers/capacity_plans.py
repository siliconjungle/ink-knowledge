"""Physical reservations authored from ordinary, source-bound cardinality proofs."""
import copy
from producers.planning_recipes import row
from producers.semantic_laws import value,var,op,term

def expression(term,parameters,depth=0):
    """Reify pure, binder-free count expressions; admission remains in core.

    There is no per-algorithm formula recogniser. A theorem supplies the whole
    bound, built from ordinary typed operations and input parameters.
    """
    if depth>64:raise ValueError('capacity expression depth')
    node=term['node']
    if isinstance(node,dict):
        if 'Free'in node and node['Free']in parameters:return {'Var':node['Free']}
        if 'Word'in node:return {'Num':node['Word']}
        if 'Op'in node:
            name,args=node['Op'];args=[expression(t,parameters,depth+1)for t in args]
            if name.startswith('binary:')and len(args)==2:return {'Binary':[name[7:],*args]}
            if name.startswith('call:'):return {'Call':[name[5:],args]}
            if name.startswith('field:')and len(args)==1:return {'Field':[args[0],name[6:]]}
            if name.startswith('method:')and args:return {'Method':[args[0],name[7:],args[1:]]}
    raise ValueError('capacity needs a pure, binder-free source expression')

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
            capacity=node[1][1]
            expected=op(value('Bool'),'binary:<=',count(var(value(f['result']),fact['subject_variable'])),capacity)
            if fact['context']!=expected or fact['value']!=term(value('Bool'),{'Bool':True}):continue
            try:formula=expression(capacity,dict(f['params']))
            except (ValueError,KeyError,TypeError):continue
            plan=copy.deepcopy(context.get('physical')or dict(schema=1,semantics='ink-physical-plan-v1',input_core_sha256=context['source'],tables='ordered',definitions='shared',borrow_reads=[],borrow_rows=[],packed_datatypes=[],memo_functions=[]))
            evidence=dict(packet,facts=[fact]);reservations=[r for r in plan.get('reservations',[]) if r['function']!=f['name']]
            plan['reservations']=[*reservations,dict(function=f['name'],capacity=formula,evidence=evidence)]
            yield row('physical',plan,'proved result capacity/'+f['name'])
