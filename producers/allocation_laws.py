"""Allocation policies as ordinary exact-integer cardinality theorems.

No allocator name or strategy provides semantic authority. The consumer checks
these theorems against the exact source before using their right-hand formula.
"""
from producers.semantic_laws import value,var,op,term,law
from ink_knowledge import Store,semantic_entry,identity

def examples():
 result={}
 for name,t in [('u32','U32'),('i32','I32'),('u64','U64'),('f32','F32'),('bool','Bool'),('string','String'),('int','Int'),('nested-u32',{'List':'U32'})]:
  seq=value({'List':t});xs=var(seq,'xs');ys=var(seq,'ys');b=value('Bool');count=lambda x:op(value('Int'),'call:count',x)
  formula=op(value('Int'),'binary:+',count(xs),count(ys))
  proof={'Induction':dict(variable='xs',names=['head','tail'],base={'Linear':dict(premises=[])},step={'Linear':dict(premises=[[0,1]])})}
  result['allocation/concat-capacity-'+name]=law(dict(xs=seq,ys=seq),op(b,'binary:<=',count(op(seq,'method:concat',xs,ys)),formula),term(b,{'Bool':True}),proof)
 return result

def publish(root):
 rows=[(n,semantic_entry(l))for n,l in examples().items()]
 return Store(root).extend([o for _,o in rows],{n:identity(o)for n,o in rows})

if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);args=p.parse_args();print(publish(args.root).snapshot_id)
