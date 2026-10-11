"""Maintain exact ordered query contributions in an ordinary data column.

A cell stores the query's contribution for one row (possibly empty). A universal
induction proves that concatenating these cells equals the unchanged query.
Queries with cross-row/global dependencies fail this authoring tactic.
"""
from action_replacement import var,call,cons,convert,trans
from point_delta import sub,normal,equality,choice
from representations import match


def contribution(model,query,table,row_sort,function,objects):
    action=model['actions'][query]
    normal_case=action['case']['normal'].get('Construct',{})
    if len(action['params'])!=2 or normal_case.get('constructor')!=0 or normal_case['arguments'][1]!={'Bool':False}:
        raise ValueError('ordered column needs a parameterless unchanged query')
    reply=normal_case['arguments'][0]
    from point_delta import free_variables
    if free_variables(reply)-{action['case']['bindings'][0]}:
        raise ValueError('ordered contribution captures another logical root')
    result=objects[action['result']['Data']]['payload']['declaration']['Datatype']['constructors'][0]['fields'][0]
    if not isinstance(result,dict)or 'Data'not in result:raise ValueError('ordered result must be a list')
    cs=objects[result['Data']]['payload']['declaration']['Datatype']['constructors']
    if len(cs)!=2 or cs[0]['fields'] or len(cs[1]['fields'])!=2 or cs[1]['fields'][1]!='SelfType':
        raise ValueError('ordered result must use a finite list carrier')
    key_sort=objects[table['datatype']]['payload']['declaration']['Datatype']['constructors'][1]['fields'][0]
    def empty(sort):
        if sort=='U64':return {'U64':0}
        if sort=='Bool':return {'Bool':False}
        if isinstance(sort,dict)and 'Data'in sort:
            constructors=objects[sort['Data']]['payload']['declaration']['Datatype']['constructors']
            for i,c in enumerate(constructors):
                if 'SelfType'not in c['fields']:return cons(sort['Data'],i,[empty(s)for s in c['fields']])
        raise ValueError('ordered contribution has no finite key inhabitant')
    nil=cons(table['datatype'],0,[])
    singleton=cons(table['datatype'],1,[empty(key_sort),var('view_row'),nil])
    q=lambda rows:sub(reply,{action['case']['bindings'][0]:rows})
    mapper=function([['view_row',row_sort]],result,q(singleton))
    return result,mapper,q


def prove_read(table,root_sort,cid,columns,index,selector,mapper,result,query,function,theorem,objects):
    output=result['Data'];outer=columns[index]['Data']
    append=function([['view_prefix',result],['view_rest',result]],result,
        match(var('view_prefix'),[([],var('view_rest')),(['view_head','view_tail'],cons(output,1,[var('view_head'),{'SelfCall':[var('view_tail'),var('view_rest')]}]))]),recursive=0)
    flatten=function([['view_cells',columns[index]]],result,match(var('view_cells'),[
        ([],cons(output,0,[])),(['view_cell','view_cells_tail'],call(append,[var('view_cell'),{'SelfCall':[var('view_cells_tail')]}]))]),recursive=0)
    ns=['view_column_'+str(i)for i in range(len(columns))]
    read=function([['columns',{'Data':cid}]],result,match(var('columns'),[(ns,call(flatten,[var(ns[index])]))]))
    direct=lambda rows:call(flatten,[call(selector,[rows])])
    rows=var('view_rows');tail=var('view_rows_tail');key=var('view_key');row=var('view_value')
    nil=cons(table['datatype'],0,[]);bound=cons(table['datatype'],1,[key,row,tail])
    a,z=direct(bound),query(bound)
    guards=[]
    def collect(t):
        if isinstance(t,dict):
            if 'If'in t and t['If']['condition']not in guards:guards.append(t['If']['condition'])
            for v in t.values():collect(v)
        elif isinstance(t,list):
            for v in t:collect(v)
    collect([normal(a,objects),normal(z,objects)])
    # A conditional cell contribution is exposed before its append. Splitting
    # the row predicate uses existing Boolean elimination, with no core rewrite.
    def prove(level=0,facts=()):
        if level==len(guards):return equality(a,z,objects,hyp=(direct(tail),query(tail),0),facts=facts)
        guard=guards[level]
        return {'BoolSplit':dict(condition=guard,**{'from':a,'to':z},**{
            label:prove(level+1,(*facts,(guard,{'Bool':flag},level+1)))for label,flag in [('on_false',False),('on_true',True)]})}
    left,right=direct(rows),query(rows)
    law=theorem([['view_rows',root_sort]],left,right,{'Induction':dict(variable='view_rows',**{'from':left,'to':right},cases=[
        dict(bindings=[],proof=convert(direct(nil),query(nil))),dict(bindings=['view_key','view_value','view_rows_tail'],proof=prove())])})
    return read,law
