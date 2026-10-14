"""Author a source template for independent folds with per-result captures.

Only data is emitted: private record declarations, ordinary semantic terms and
an induction proof using a supplied map-fusion theorem. No source recognizer.
"""
from ink_knowledge import entry
from producers.semantic_laws import value,arrow,var,bound,op,lam,law

def templates(map_fusion):
 from ink_planner.semantic_search import map_children
 types={n:{'Named':'$'+n}for n in ['A','E','S']}
 A,E,S=[value(types[n])for n in ['A','E','S']]
 P=value({'Named':'Lane'});LA=value({'List':types['A']});LE=value({'List':types['E']});LP=value({'List':{'Named':'Lane'}});LS=value({'List':types['S']})
 params=dict(xs=LA,envs=LE,initial=arrow(E,S),step=arrow(E,arrow(A,arrow(S,S))))
 xs,envs,initial,step=[var(params[n],n)for n in ['xs','envs','initial','step']]
 def abstract(name,sort,body):
  def walk(t,depth=0):
   node=t['node']
   if isinstance(node,dict):
    if node.get('Free')==name:return bound(t['sort'],depth)
    if 'Bound'in node and node['Bound']>=depth:return bound(t['sort'],node['Bound']+1)
   return map_children(t,lambda child:walk(child,depth+int(isinstance(node,dict)and 'Lambda'in node)))
  return lam(sort,walk(body))
 def apply(f,*args):
  for arg in args:f=op(f['sort']['Arrow'][1],'apply',f,arg)
  return f
 def map_(sequence,callback):return op(value({'List':callback['sort']['Arrow'][1]['Value']}),'method:map',sequence,callback)
 def fold(sequence,seed,callback):return op(seed['sort'],'call:foldl',sequence,seed,callback)
 def pack(e,s):return op(P,'record:Lane',e,s)
 def field(p,name,sort):return op(sort,'field:'+name,p)
 e,x,s,p,current=[var(t,n)for t,n in [(E,'environment'),(A,'item'),(S,'state'),(P,'lane'),(LP,'current')]]
 project=abstract('lane',P,field(p,'state',S))
 def lift(seed):return abstract('environment',E,pack(e,apply(seed,e)))
 def advance(item):return abstract('lane',P,pack(field(p,'environment',E),apply(step,field(p,'environment',E),item,field(p,'state',S))))
 batch=abstract('item',A,abstract('current',LP,map_(current,advance(x))))
 def separate(sequence,seed):return map_(envs,abstract('environment',E,fold(sequence,apply(seed,e),abstract('item',A,abstract('state',S,apply(step,e,x,s))))))
 def fused(sequence,seed):return map_(fold(sequence,map_(envs,lift(seed)),batch),project)
 def fusion(first,middle,last,sequence,f,g):return {'Use':dict(law=map_fusion,types={'A':first,'B':middle,'C':last},arguments=dict(xs=sequence,f=f,g=g),premises=[])}
 head=var(A,'head');tail=var(LA,'tail');updated=abstract('environment',E,apply(step,e,head,apply(initial,e)))
 def trans(middle,left,right):return {'Trans':dict(middle=middle,left=left,right=right)}
 composed=map_(envs,abstract('environment',E,apply(project,apply(lift(initial),e))))
 def eta(sort,f):return abstract('eta_argument',sort,apply(f,var(sort,'eta_argument')))
 mapped=map_(map_(envs,eta(E,lift(initial))),eta(P,project))
 base=trans(composed,'Normalize',trans(mapped,{'Sym':fusion(types['E'],{'Named':'Lane'},types['S'],envs,lift(initial),project)},'Normalize'))
 seed_composed=map_(envs,abstract('environment',E,apply(advance(head),apply(lift(initial),e))))
 seed_expanded=map_(map_(envs,eta(E,lift(initial))),eta(P,advance(head)))
 unmap=trans(seed_composed,'Normalize',trans(seed_expanded,{'Sym':fusion(types['E'],{'Named':'Lane'},{'Named':'Lane'},envs,lift(initial),advance(head))},'Normalize'))
 after=map_(fold(tail,map_(map_(envs,lift(initial)),advance(head)),batch),project)
 step_proof=trans(separate(tail,updated),'Normalize',trans(fused(tail,updated),{'GeneralizedHypothesis':dict(index=0,arguments={'initial':updated})},trans(after,{'Congruence':[{'Congruence':['Normalize',unmap,'Normalize']},'Normalize']},'Normalize')))
 proof={'GeneralizedInduction':dict(variable='xs',generalize=['initial'],names=['head','tail'],base=base,step=step_proof)}
 theorem=law(params,separate(xs,initial),fused(xs,initial),proof,dependencies=[map_fusion]);theorem['semantics']='ink-general-laws-v1'
 payload=dict(type_parameters=['A','E','S'],definitions=dict(functions=[],ids=[],records={'Lane':[['environment',types['E']],['state',types['S']]]},enums={}),law=theorem)
 return [dict(name='captured-independent-folds',object=entry('definition','ink-source-algorithm-v1',payload,[map_fusion]))]

if __name__=='__main__':
 import argparse
 from ink_knowledge.source_algorithms import publish
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--root',required=True)
 parser.add_argument('--map-fusion',required=True,help='Snapshot-owned general map-fusion law; every use still replays its proof')
 args=parser.parse_args()
 print(publish(args.root,templates(args.map_fusion)).snapshot_id)
