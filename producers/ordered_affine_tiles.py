"""Checked ordered affine-fold tiling proposals, with a literal unbounded suffix.

Construction is untrusted: every law replays in Ink. Source order and wrapping
arithmetic are preserved. Dimensions are compile-time choices, never runtime
adaptation. Proof does not establish device eligibility or profitability.
"""
import argparse,gzip,json,subprocess,tempfile
from importlib.resources import files
from pathlib import Path
from ink_knowledge import Store,canonical,identity,semantic_entry
from producers.semantic_laws import value,var,word,op,lam,bound,binary,term,arrow,law

def author(tile_size=4096,tiles=16):
 if type(tile_size)is not int or type(tiles)is not int or not 1<=tiles<=16 or not 1<=tile_size or tile_size*tiles>4294967295:
  raise ValueError('bounded positive tile dimensions required')
 support=json.loads(gzip.decompress(files('producers').joinpath('data/ordered-affine-support.json.gz').read_bytes()))
 support_names=support['names']
 objects=dict(support['objects'])
 u=value('U32');l=value({'List':'U32'})
 xs=var(l,'xs');seed=var(u,'seed');k=var(u,'k');head=var(u,'head');tail=var(l,'tail')
 step=lam(u,lam(u,binary('+',bound(u,1),binary('*',bound(u,0),k))))
 prod=lam(u,lam(u,binary('*',bound(u,0),k)))
 f=lambda a,z:op(u,'call:foldr',a,z,step)
 p=lambda a:op(u,'call:foldr',a,word('U32',1),prod)
 target=lambda a,z:binary('+',f(a,word('U32',0)),binary('*',z,p(a)))
 proof={'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step='Normalize')}
 affine=law(dict(xs=l,seed=u,k=u),f(xs,seed),target(xs,seed),proof)
 zero=word('U32',0);one=word('U32',1);maxv=word('U32',4294967295);nil=term(l,'Nil')
 compare=lambda name,x,y:op(value('Bool'),'binary:'+name,x,y)
 choose=lambda c,x,y:op(l,'call:choose',c,x,y)
 drop=lambda x,n:op(l,'method:drop',x,n)
 chain=lambda mid,left,right:{'Trans':dict(middle=mid,left=left,right=right)}
 # Fixed-width affine carriers use the existing Vec2 type, never a new primitive.
 vec=value({'Vector':['U32',2]}); lv=value({'List':{'Vector':['U32',2]}})
 field=lambda x,n:op(u,'field:'+n,x)
 pair=lambda x,y:op(vec,'call:vec2',x,y)
 step_pair=lam(u,lam(vec,pair(binary('+',bound(u,1),binary('*',field(bound(vec,0),'x'),k)),binary('*',field(bound(vec,0),'y'),k))))
 # Keep the carrier's word width explicit when the ordinary source reifier
 # reconstructs the constructor (unconstrained numeric literals default wide).
 typed_zero=binary('-',k,k)
 summary=lambda a:op(vec,'call:foldr',a,pair(typed_zero,binary('+',typed_zero,one)),step_pair)
 objects[identity(semantic_entry(affine))]=semantic_entry(affine)
 named={}
 def add(name,row):
  obj=semantic_entry(row);key=identity(obj);objects[key]=obj;named[name]=key;return key
 for label,other in [('x',lambda a:f(a,zero)),('y',p)]:
  add('summary_'+label,law(dict(xs=l,k=u),field(summary(xs),label),other(xs),{'Induction':dict(variable='xs',names=['head','tail'],base='Normalize',step='Normalize')}))
 def useid(key,args):return {'Use':dict(law=key,arguments=args,premises=[])}
 def use_name(name,args):return useid(named[name],args)
 apply_summary=lambda a,z:binary('+',field(summary(a),'x'),binary('*',z,field(summary(a),'y')))
 applyproof=chain(target(xs,seed),useid(identity(semantic_entry(affine)),dict(xs=xs,k=k,seed=seed)),{'Congruence':[{'Sym':use_name('summary_x',dict(xs=xs,k=k))},{'Congruence':['Normalize',{'Sym':use_name('summary_y',dict(xs=xs,k=k))}]}]})
 add('apply_summary',law(dict(xs=l,k=u,seed=u),f(xs,seed),apply_summary(xs,seed),applyproof,dependencies=[identity(semantic_entry(affine)),named['summary_x'],named['summary_y']]))
 # Instantiate the general ordered split law; the eta-expanded callback is part
 # of the authored statement and is transported by ordinary normalization.

 split_id=support_names['slice_split']
 n=var(u,'n');take=lambda a,n:op(l,'method:take',a,n)
 wrapped=lam(u,lam(u,op(u,'apply',op(arrow(u,u),'apply',step,bound(u,1)),bound(u,0))))
 wf=lambda a,z:op(u,'call:foldr',a,z,wrapped)
 sp={'Use':dict(law=split_id,types=dict(A='U32',S='U32'),arguments=dict(xs=xs,n=n,seed=seed,step=step),premises=[])}
 splitproof=chain(wf(xs,seed),'Normalize',chain(wf(take(xs,n),wf(drop(xs,n),seed)),sp,'Normalize'))
 splitrow=law(dict(xs=l,n=u,seed=u,k=u),f(xs,seed),f(take(xs,n),f(drop(xs,n),seed)),splitproof,dependencies=[split_id]);splitrow['semantics']='ink-general-laws-v1'
 add('split_affine',splitrow)
 # Recover the already admitted conditional slice composition statement.
 drop_id=support_names['drop_composition']
 W=tile_size;N=tiles
 word32=lambda n:word('U32',n)
 combine=lam(vec,lam(u,binary('+',field(bound(vec,1),'x'),binary('*',bound(u,0),field(bound(vec,1),'y')))))
 mapper=lam(u,summary(take(drop(xs,bound(u,0)),word32(W))))
 def offsets(i):
  out=term(l,'Nil')
  for j in reversed(range(i,N)):out=term(l,{'Cons':[word32(j*W),out]})
  return out
 end=f(drop(xs,word32(N*W)),seed)
 def out(i):return op(u,'call:foldr',op(lv,'method:map',offsets(i),mapper),end,combine)
 params=dict(xs=l,seed=u,k=u)
 add('tiles_'+str(N),law(params,f(drop(xs,word32(N*W)),seed),out(N),'Normalize'))
 for i in reversed(range(N)):
  off=word32(i*W);width=word32(W);nextoff=word32((i+1)*W)
  oldtail=drop(drop(xs,off),width);newtail=drop(xs,nextoff)
  cond=compare('<=',off,binary('-',maxv,width))
  oldguard=choose(cond,oldtail,nil);newguard=choose(cond,drop(xs,binary('+',off,width)),nil)
  dropproof=chain(oldguard,'Normalize',chain(newguard,useid(drop_id,dict(xs=xs,a=off,b=width)),'Normalize'))
  did=add('drop_'+str(i),law(dict(xs=l),oldtail,newtail,dropproof,dependencies=[drop_id]))
  chunk=take(drop(xs,off),width)
  first=f(chunk,f(oldtail,seed));second=f(chunk,f(newtail,seed));third=apply_summary(chunk,f(newtail,seed));last=apply_summary(chunk,out(i+1))
  splituse=use_name('split_affine',dict(xs=drop(xs,off),n=width,seed=seed,k=k))
  tailproof={'Congruence':[useid(did,dict(xs=xs)),'Normalize','Normalize']}
  secondproof={'Congruence':['Normalize',tailproof,'Normalize']}
  applyuse=use_name('apply_summary',dict(xs=chunk,seed=f(newtail,seed),k=k))
  nextuse=use_name('tiles_'+str(i+1),dict(xs=xs,seed=seed,k=k))
  lastproof={'Congruence':['Normalize',{'Congruence':[nextuse,'Normalize']}]}
  proof=chain(first,splituse,chain(second,secondproof,chain(third,applyuse,chain(last,lastproof,'Normalize'))))
  add('tiles_'+str(i),law(params,f(drop(xs,off),seed),out(i),proof,dependencies=[named['split_affine'],did,named['apply_summary'],named['tiles_'+str(i+1)]]))
 rootproof=chain(f(drop(xs,zero),seed),'Normalize',use_name('tiles_0',dict(xs=xs,seed=seed,k=k)))
 root=law(params,f(xs,seed),out(0),rootproof,dependencies=[named['tiles_0']])
 add('ordered_affine_tiles_u32',root)
 return objects,named,named['ordered_affine_tiles_u32']

def specialize(subject,core):
 """Offer the checked construction through ordinary planner discovery.

 Matching is only a search filter. Admission and measured selection remain
 independent, and the serial source stays available for small workloads.
 """
 from ink_planner.semantic_search import positions,match
 objects,names,root=author()
 row=objects[root]['payload']
 if not any(match(row['from'],site,row['params'],{}) for body in subject.get('functions',{}).values() for _,site in positions(body)):
  return []
 rows=[];visited=set()
 def visit(key):
  if key in visited:return
  obj=objects[key]
  for dependency in obj['dependencies']:visit(dependency)
  visited.add(key)
  rows.append(('ordered_affine/'+key,dict(obj['payload'],schema=1,semantics=obj['semantics'],dependencies=obj['dependencies'])))
 visit(root)
 return rows

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--compiler',type=Path,required=True)
 p.add_argument('--tile-size',type=int,default=4096);p.add_argument('--tiles',type=int,default=16)
 p.add_argument('-o',type=Path,required=True);a=p.parse_args()
 objects,names,root=author(a.tile_size,a.tiles)
 with tempfile.TemporaryDirectory(prefix='ink-affine-tiles-')as td:
  d=Path(td);source=d/'subject.ink';core=d/'core.json';view=d/'view.json'
  source.write_text('module Affine;fn hash(xs:List<u32>,seed:u32,k:u32)->u32{return foldr(xs,seed,fn(x)=>fn(acc)=>x+acc*k);}')
  staged=Store.publish(d/'store',objects.values(),{'ordered_affine_tiles_u32':root})
  view.write_bytes(canonical(staged.bundle([root])))
  for command in [[a.compiler.resolve(),'emit-core',source,'-o',core],[a.compiler.resolve(),'knowledge-check',core,view]]:
   result=subprocess.run(list(map(str,command)),capture_output=True,text=True,timeout=180)
   if result.returncode:raise RuntimeError(result.stderr)
  published=Store.publish(a.o,objects.values(),{'ordered_affine_tiles_u32':root})
  (a.o/'view.json').write_bytes(view.read_bytes())
  (a.o/'admission.json').write_text(result.stdout)
  (a.o/'dimensions.json').write_text(json.dumps(dict(tile_size=a.tile_size,tiles=a.tiles,frontier=a.tile_size*a.tiles,tail='literal ordered fold'))+'\n')
  print(json.dumps(dict(status='checked',root=root,snapshot=published.snapshot['root'])))

if __name__=='__main__':main()
