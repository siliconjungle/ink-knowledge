"""Database-authored graph strategies; generic checker validates every release."""
from ink_knowledge import identity
from producers.planning_recipes import row

def release_points(graph,input_count=None):
    last={s['id']:i for i,s in enumerate(graph['stages'])}
    for i,s in enumerate(graph['stages']):
        for ref in s['arguments']:
            if 'Stage' in ref:last[ref['Stage']]=i
    if 'Stage' in graph['output']:last[graph['output']['Stage']]=len(graph['stages'])
    input_last={}
    if input_count is not None:input_last={i:0 for i in range(input_count)}
    for i,s in enumerate(graph['stages']):
        for ref in s['arguments']:
            if 'Input' in ref:input_last[ref['Input']]=i
    if 'Input' in graph['output']:input_last[graph['output']['Input']]=len(graph['stages'])
    return [dict(after=s['id'],values=sorted(k for k,v in last.items() if v==i),inputs=sorted(k for k,v in input_last.items() if v==i))
        for i,s in enumerate(graph['stages']) if any(v==i for v in last.values()) or any(v==i for v in input_last.values())]

def propose(context):
    graph=context['route'];entry=next((f for f in context.get('core',{}).get('program',{}).get('functions',[]) if f['name']==graph.get('entry')),None)
    base=dict(schema=1,semantics='ink-graph-resources-v1',route_sha256=identity(graph),releases=release_points(graph,len(entry['params']) if entry else None),admission=None)
    yield row('resources',base,'release final-use graph values')
    profile=context.get('usage_profile')
    if not profile:return
    peak=profile.get('peak_pending',0);size=profile.get('peak_pending_bytes',0)
    if not peak or not size:return
    # Profile-derived hypotheses, never universal size/rate assumptions. Actual
    # dynamic credits enforce the compiled limit and report overload explicitly.
    for factor in (1,2,4):
        admission=dict(max_pending=min(1_000_000,peak*factor),max_pending_bytes=min(9_007_199_254_740_991,size*factor))
        yield row('resources',dict(base,admission=admission),'observed credits x'+str(factor))
