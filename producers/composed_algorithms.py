"""Publish an algorithm assembled from existing database families.

This authors data only. Discovery, imports, extension and proof replay use the
same generic producer as any other source algorithm.
"""
import copy,json
from pathlib import Path
from ink_knowledge import entry,identity,canonical
from ink_knowledge.source_algorithms import publish
from ink_knowledge.law_templates import substitute_types

def templates():
    rows=json.loads((Path(__file__).resolve().parents[1]/'libraries/source-algorithms.json').read_bytes())
    partition=rows[1]['object'];count=rows[2]['object']
    law=copy.deepcopy(count['payload']['law']);partition_law=substitute_types(partition['payload']['law'],{'A':'U32'})
    middle=copy.deepcopy(law['from']);source=copy.deepcopy(middle)
    source['node']['Op'][1][0]['node']['Op'][1][0]=partition_law['from']
    xs=copy.deepcopy(law['params']['xs']);xs=dict(sort=xs,node={'Free':'xs'})
    count_arg=dict(sort={'Value':'U32'},node={'Free':'count'})
    partition_result=copy.deepcopy(partition_law['to']);partition_result['node']['Op'][0]='call:partition_helper'
    undo={'Trans':dict(middle=partition_result,left={'Use':dict(law='$partition',arguments=dict(xs=xs,count=count_arg),premises=[])},right='Normalize')}
    law['from']=source;law['to']['node']['Op'][0]='call:count_helper';law['params']['count']={'Value':'U32'}
    law['proof']={'Trans':dict(middle=middle,left={'Congruence':[{'Congruence':[undo,'Normalize']}]},right={'Use':dict(law='$count',arguments={n:dict(sort=s,node={'Free':n})for n,s in count['payload']['law']['params'].items()},premises=[])})}
    payload=dict(type_parameters=[],definitions=dict(functions=[],ids=[],records={},enums={}),law=law,imports={
        '$partition':dict(algorithm=identity(partition),types={'A':'U32'},exports={'partition_helper':'unwrap'}),
        '$count':dict(algorithm=identity(count),types={},exports={'count_helper':'ge_count'})})
    obj=entry('definition','ink-source-algorithm-v1',payload,[identity(partition),identity(count)])
    return [dict(name='partition-filter-count-composition',object=obj)]

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--export',type=Path);a=p.parse_args();rows=templates()
    if a.export:a.export.write_bytes(canonical(rows)+b'\n')
    print(publish(a.root,rows).snapshot_id)
