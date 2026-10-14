"""Measured native inlining choices for hot source helpers with large carriers.

These are source-bound code-generation hints, not semantic replacements. No
domain recognizer, correctness fact, or guaranteed compiler inlining follows
from a call frequency or carrier-size estimate. The checker admits the exact
source sites and the usual offline acquisition decides profitability.
"""
import copy

def choices(core,frequencies,counts=(8,24,64),max_body=4096):
 records=core['program']['records']
 def words(t,seen=frozenset()):
  if isinstance(t,str):return 3 if t=='String'else 1
  if not isinstance(t,dict):return 1
  if 'Named'in t:
   n=t['Named']
   return 1 if n in seen else min(512,sum(words(v,seen|{n})for _,v in records.get(n,[])))
  return 3 if set(t)&{'Buffer','List','Map','Table'}else 1
 def size(body):
  pending=[body];n=0
  while pending:
   x=pending.pop();n+=1
   if n>max_body:return n
   if isinstance(x,dict):pending.extend(x.values())
   elif isinstance(x,list):pending.extend(x)
  return n
 ranked=[]
 for f in core['program']['functions']:
  carrier=max([words(f['result']),*[words(t)for _,t in f['params']]])
  count=frequencies.get('call:'+f['name'],0);body=size(f['body'])
  if carrier<6 or body>max_body or count==0:continue
  ranked.append((-carrier*count/max(1,body),f['name']))
 ranked.sort();seen=set()
 for count in counts:
  if type(count)is not int or not 1<=count<=256:raise ValueError('native inlining proposal budget')
  names=tuple(sorted(name for _,name in ranked[:count]))
  if not names or names in seen:continue
  seen.add(names);yield list(names)

def propose(context,counts=(8,24,64),max_body=4096):
 if context.get('representation')or context.get('emit_target','rust')not in {'rust','rust-wasm'}:return
 if context.get('physical'):
  bases=[context['physical']]
 else:
  from producers.readonly_borrows import scoped_candidates
  bases=[r['step']['package']for r in scoped_candidates(context,['all-observations'])]
 for names in choices(context['core'],context.get('frequencies',{}),counts,max_body):
  for base in bases:
   if names==base.get('inline_functions',[]):continue
   package=copy.deepcopy(base);package['inline_functions']=names
   yield dict(status='proposal',label='native-function-inline/'+str(len(names)),step=dict(kind='physical',package=package))
