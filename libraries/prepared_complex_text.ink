module ink.knowledge.prepared_complex_text;
import "std:prepared_text" as text;
// Complex prepared line geometry, ported from Pretext 0a27bbe0, MIT.
// Copyright (c) 2026 Pretext contributors. See notices/pretext-LICENSE.txt.
// Measurement/segmentation stay explicit inputs. No floating-point narrowing.
enum HyphenRetreat { ReducedWidth, FullWidth, FullWidthOrFirst, }
enum OpeningFit { Start, Placed, Both, }
enum HardBreakRetreat { Item, Fit, LastGrapheme, }
record Profile {
 epsilon:f64, hangTabs:Bool, hangsSpacesPerTextFrame:Bool,
 testsHyphenBeforeAtomic:Bool, zeroWidthGlueTakesLine:Bool, tabsInAppUnits:Bool,
 hyphenRetreat:HyphenRetreat, openingFit:OpeningFit, hardBreakRetreat:HardBreakRetreat,
}
record Items {
 hyphenWidths:Option<List<f64>>, hyphenRooms:Option<List<f64>>,
 itemEndHalts:Option<List<f64>>, openingEdges:Option<List<f64>>,
 emptyObjectSpaces:Option<List<f64>>, emptyObjectReturns:Option<List<u32>>,
 tabStops:Option<List<f64>>, minimumTabs:Option<List<f64>>,
}
record Data {
 base:text.Data, profile:Profile, items:Option<Items>,
 letterSpacing:f64, hyphenWidth:f64, hyphenContexts:Option<List<f64>>,
 tabStop:f64, minimumTab:f64,
}
abstract record Prepared { data:Data, budget:u32, }

fn absent()->u32 {return 4294967295;}
fn scalar(xs:Option<List<f64>>,i:u32)->f64 {return xs.fold(fn(xs)=>xs.at_or(i,0f64),fn(u)=>0f64);}
fn present(xs:Option<List<f64>>)->Bool {return xs.fold(fn(xs)=>true,fn(u)=>false);}
fn values(xs:Option<List<f64>>)->List<f64> {return xs.fold(fn(xs)=>xs,fn(u)=>[]);}
fn kind(d:Data,i:u32)->u32 {return d.base.flags.at_or(i,0)&15;}
fn breaks_after(k:u32)->Bool {return k==1 || k==2 || k==3 || k==4 || k==5;}
fn hangs_kind(d:Data,k:u32)->Bool {return k==4 || (d.profile.hangTabs && k==5);}
fn nan()->f64 {return f64_from_bits(9221120237041090560);}
fn negative_zero()->f64 {return f64_from_bits(9223372036854775808);}
// Math.min/max preserve zero signs and propagate NaN. A plain ordered choose
// would change the upstream geometry at these exceptional values.
fn minimum(a:f64,b:f64)->f64 {
 if is_nan(a) || is_nan(b) {return nan();}
 if a==0f64 && b==0f64 {return choose(((f64_bits(a)|f64_bits(b))&9223372036854775808)!=0,negative_zero(),0f64);}
 return choose(a<b,a,b);
}
fn maximum(a:f64,b:f64)->f64 {
 if is_nan(a) || is_nan(b) {return nan();}
 if a==0f64 && b==0f64 {return choose(((f64_bits(a)&f64_bits(b))&9223372036854775808)!=0,negative_zero(),0f64);}
 return choose(a>b,a,b);
}
// JavaScript round: ties toward +infinity, with -0 on [-0.5,0).
// floor(x+0.5) rounds twice at the representable neighbor below 0.5.
fn round_js(x:f64)->f64 {
 if !is_finite(x) || x==0f64 {return x;}
 let lo=floor(x);let result=choose(x-lo<0.5f64,lo,lo+1f64);
 return choose(result==0f64 && x<0f64,negative_zero(),result);
}
fn tab_advance(position:f64,stop:f64,minimumAdvance:f64,appUnits:Bool)->f64 {
 if appUnits {
  let stop=round_js(stop*60f64);
  if stop<=0f64 {return 0f64;}
  let x=round_js(position*60f64);
  return (ceil((x+round_js(minimumAdvance*120f64)/2f64)/stop)*stop-x)/60f64;
 }
 if stop<=0f64 {return 0f64;}
 let past=position-floor(position/stop)*stop;let advance=stop-past;
 return choose(advance<minimumAdvance,advance+stop,advance);
}
fn item_tab(d:Data,items:Items,i:u32,lineWidth:f64)->f64 {
 let stop=items.tabStops.fold(fn(xs)=>xs.at_or(i,0f64),fn(u)=>d.tabStop);
 let minimumAdvance=items.minimumTabs.fold(fn(xs)=>xs.at_or(i,0f64),fn(u)=>d.minimumTab);
 let endEdge=scalar(d.base.insideExtras,i)/2f64;
 return tab_advance(lineWidth-endEdge,stop,minimumAdvance,d.profile.tabsInAppUnits)+d.base.widths.at_or(i,0f64);
}
fn opening(d:Data,i:u32)->f64 {return d.items.fold(fn(items)=>scalar(items.openingEdges,i),fn(u)=>0f64);}
fn halt(d:Data,i:u32)->Bool {return d.items.fold(fn(items)=>scalar(items.itemEndHalts,i)!=0f64,fn(u)=>false);}
fn room(d:Data,i:u32,reserved:f64)->f64 {
 return d.items.fold(fn(items)=>choose(i==absent(),reserved,
   items.hyphenRooms.fold(fn(xs)=>xs.at_or(i,0f64),fn(u)=>reserved)),fn(u)=>reserved);
}
fn finite(xs:List<f64>)->Bool {return foldl(xs,true,fn(x)=>fn(ok)=>ok && is_finite(x));}
fn sized(xs:Option<List<f64>>,n:u32)->Bool {return xs.fold(fn(xs)=>count(xs)<=1000001 && length(xs)==n && finite(xs),fn(u)=>true);}
fn valid_items(items:Items,n:u32)->Bool {
 return sized(items.hyphenWidths,n) && sized(items.hyphenRooms,n+1) && sized(items.itemEndHalts,n) &&
  sized(items.openingEdges,n) && sized(items.emptyObjectSpaces,n) && sized(items.tabStops,n) && sized(items.minimumTabs,n) &&
  items.emptyObjectReturns.fold(fn(xs)=>count(xs)<=1000000 && length(xs)==n && foldl(xs,true,fn(x)=>fn(ok)=>ok && x<=1),fn(u)=>true) &&
  (present(items.emptyObjectSpaces)==items.emptyObjectReturns.fold(fn(xs)=>true,fn(u)=>false));
}
record Shape { valid:Bool, budget:u32, index:u32, }
fn shape_step(d:Data,maximumSize:u32,advance:Option<List<f64>>,s:Shape)->Shape {
 let i=s.index;let flags=d.base.flags.at_or(i,256);let k=flags&15;
 let size=advance.fold(fn(xs)=>length(xs),fn(u)=>0);
 let valid=s.valid && flags<=255 && k<=9 &&
  advance.fold(fn(xs)=>count(xs)>0 && count(xs)<=1000000 && length(xs)<=maximumSize && finite(xs),fn(u)=>true) &&
  d.base.graphemeStartExtras.fold(fn(es)=>es.at_or(i,None).fold(
   fn(es)=>advance.fold(fn(xs)=>count(es)==count(xs) && finite(es),fn(u)=>false),fn(u)=>true),fn(u)=>true);
 let fits=size<=maximumSize-s.budget;
 return Shape{valid:valid && fits,budget:choose(fits,s.budget+size,s.budget),index:i+1};
}
fn checked_budget(d:Data,maximumSize:u32)->Option<u32> {
 if maximumSize==0 || maximumSize>1000000 || count(d.base.widths)>1000000 || length(d.base.widths)>maximumSize || !finite(d.base.widths) ||
  !is_finite(d.profile.epsilon) || d.profile.epsilon<0f64 || !is_finite(d.letterSpacing) || !is_finite(d.hyphenWidth) ||
  !is_finite(d.tabStop) || !is_finite(d.minimumTab) {return None;}
 let n=length(d.base.widths);
 if count(d.base.flags)>1000000 || length(d.base.flags)!=n || count(d.base.advances)>1000000 || length(d.base.advances)!=n ||
  !sized(d.base.startExtras,n) || !sized(d.base.endTrims,n) || !sized(d.base.overflowTrims,n) || !sized(d.base.insideExtras,n) ||
  !sized(d.base.fillExtras,n) || !sized(d.hyphenContexts,n) ||
  !d.base.graphemeStartExtras.fold(fn(xs)=>count(xs)<=1000000 && length(xs)==n,fn(u)=>true) ||
  !d.items.fold(fn(items)=>valid_items(items,n),fn(u)=>!present(d.base.insideExtras) && !present(d.base.fillExtras)) {return None;}
 let s=foldl(d.base.advances,Shape{valid:true,budget:n,index:0},fn(a)=>fn(s)=>shape_step(d,maximumSize,a,s));
 return choose(s.valid,Some(s.budget),None);
}
fn prepare(d:Data,maximumSize:u32)->Result<Prepared,String> {
 return checked_budget(d,maximumSize).fold(fn(n)=>Ok(Prepared{data:d,budget:n}),fn(u)=>Err("invalid complex prepared text"));
}
fn valid(p:Prepared)->Bool {return checked_budget(p.data,1000000).fold(fn(n)=>n==p.budget,fn(u)=>false);}

record Normalize { index:u32, chunkStart:Bool, done:Bool, available:Bool, }
fn normalize_step(d:Data,s:Normalize)->Normalize {
 let n=length(d.base.widths);let k=kind(d,s.index);
 if k==8 {
  if s.chunkStart {return Normalize{..s,done:true,available:true};}
  return Normalize{index:s.index+1,chunkStart:true,done:s.index+1>=n,available:false};
 }
 if k==1 || k==3 || (k==2 && !s.chunkStart) {
  return Normalize{..s,index:s.index+1,done:s.index+1>=n,available:false};
 }
 return Normalize{..s,done:true,available:true};
}
fn normalize(d:Data,c:text.Cursor)->Option<text.Cursor> {
 let n=length(d.base.widths);
 if c.segment>=n {return None;}
 if c.grapheme>0 {return Some(c);}
 let initial=Normalize{index:c.segment,chunkStart:c.segment==0 || kind(d,c.segment-1)==8,done:false,available:false};
 let s=repeat_until(n+1,initial,fn(s)=>s.done,fn(i)=>fn(s)=>normalize_step(d,s));
 return choose(s.available,Some(text.Cursor{segment:s.index,grapheme:0}),None);
}
record Config { d:Data, n:u32, available:f64, fit:f64, reserved:f64, }
fn config(d:Data,width:f64)->Config {
 let width=choose(is_nan(width),f64_from_bits(9218868437227405312),width);let available=maximum(0f64,width);
 return Config{d:d,n:length(d.base.widths),available:available,fit:available+d.profile.epsilon,
  reserved:choose(d.profile.hyphenRetreat==HyphenRetreat.ReducedWidth,d.hyphenWidth,0f64)};
}
record Scan {
 i:u32, width:f64, content:Bool, lineEnd:text.Cursor, pending:u32, pendingWidth:f64,
 fitBreak:u32, fitPaint:f64, hangEnd:u32, hangStart:f64, hangStays:Bool, hangEdges:f64,
 trim:f64, zeroPrefix:Bool, afterControl:Bool, end:u32, endG:u32, endWidth:f64,
 returnsHyphen:Bool, decided:Bool,
}
record Segment {
 i:u32, flags:u32, kind:u32, spaced:Bool, breakAfter:Bool, startG:u32,
 width:f64, leading:f64, advance:f64, endTrim:f64, fitAdvance:f64, hangs:Bool,
}
fn next(s:Scan)->Scan {return Scan{..s,i:s.i+1};}
fn stop(s:Scan,end:u32,g:u32,width:f64)->Scan {return Scan{..s,end:end,endG:g,endWidth:width,decided:true};}
fn end_of_source(s:Scan,consumed:u32)->Scan {
 let pending=s.pending==consumed && s.lineEnd.grapheme==0;
 return Scan{..s,end:consumed,endG:0,endWidth:choose(pending,s.pendingWidth,s.width-s.trim),returnsHyphen:pending,decided:true};
}
fn stays_after_object(c:Config,start:u32)->Bool {
 let after=repeat_until(c.n,start+1,fn(i)=>i>=c.n || !hangs_kind(c.d,kind(c.d,i)),fn(j)=>fn(i)=>i+1);
 return after==c.n || kind(c.d,after)!=5;
}
fn segment(c:Config,start:text.Cursor,s:Scan)->Segment {
 let i=s.i;let flags=c.d.base.flags.at_or(i,0);let k=flags&15;let spaced=(flags&16)!=0;
 let afterControl=!spaced;
 let gap=choose(c.d.letterSpacing!=0f64 && s.content && !s.zeroPrefix && !s.afterControl,c.d.letterSpacing,0f64);
 let leading=choose(c.d.letterSpacing!=0f64 && (spaced || k==7 || k==5 || k==9 || opening(c.d,i)!=0f64),gap,0f64);
 let width=choose(k!=5,c.d.base.widths.at_or(i,0f64),c.d.items.fold(
  fn(items)=>item_tab(c.d,items,i,choose(s.content,s.width+leading,scalar(c.d.base.startExtras,i))),
  fn(u)=>tab_advance(s.width+leading,c.d.tabStop,c.d.minimumTab,c.d.profile.tabsInAppUnits)));
 let breakAfter=breaks_after(k);
 let contribution=width+choose(spaced,c.d.letterSpacing,0f64);
 let fitAdvance=choose(c.d.letterSpacing!=0f64 && !spaced && !breakAfter && k!=7,gap+width,
  choose(choose(breakAfter,k==5,width!=0f64 || k==7) && contribution!=0f64,leading+contribution,0f64));
 return Segment{i:i,flags:flags,kind:k,spaced:spaced,breakAfter:breakAfter,startG:choose(i==start.segment,start.grapheme,0),
  width:width,leading:leading,advance:leading+width,endTrim:scalar(c.d.base.endTrims,i),fitAdvance:fitAdvance,
  hangs:hangs_kind(c.d,k) || (c.d.items.fold(fn(items)=>c.d.profile.hangsSpacesPerTextFrame,fn(u)=>false) && k==2 && s.hangEnd==i)};
}
fn hang(c:Config,start:text.Cursor,x:Segment,s:Scan)->Scan {
 if !x.hangs {return s;}
 let fresh=s.hangEnd!=x.i;
 let stays=fresh && c.d.items.fold(fn(items)=>x.i>start.segment && kind(c.d,x.i-1)==9,fn(u)=>false);
 let keep=choose(stays,stays_after_object(c,x.i),false);
 let pending=stays && !keep;
 let edge=opening(c.d,x.i);
 return Scan{..s,hangEnd:x.i+1,hangStart:choose(fresh,s.width-s.trim+x.leading,s.hangStart)+edge,
  hangStays:choose(fresh,keep,s.hangStays),hangEdges:choose(fresh,0f64,s.hangEdges)+edge,
  pending:choose(pending,x.i,s.pending),pendingWidth:choose(pending,s.width-s.trim,s.pendingWidth)};
}
fn soft_hyphen(c:Config,start:text.Cursor,x:Segment,s:Scan)->Scan {
 if !s.content {return next(s);}
 let withItems=c.d.items.fold(fn(items)=>true,fn(u)=>false);
 let retreat=withItems && present(c.d.hyphenContexts) && x.i>start.segment && kind(c.d,x.i-1)==9;
 let s=Scan{..s,fitBreak:choose(retreat,x.i,s.fitBreak),fitPaint:choose(retreat,s.width,s.fitPaint)};
 let hanging=withItems && c.d.profile.hangsSpacesPerTextFrame && s.hangEnd==x.i;
 let s=Scan{..s,hangEnd:choose(hanging,x.i+1,s.hangEnd),hangStart:choose(hanging,maximum(s.hangStart,minimum(s.width,c.available)),s.hangStart)};
 let width=c.d.items.fold(fn(items)=>items.hyphenWidths.fold(fn(xs)=>xs.at_or(x.i,0f64),fn(u)=>c.d.hyphenWidth),fn(u)=>c.d.hyphenWidth);
 let fits=!withItems || c.d.profile.testsHyphenBeforeAtomic || x.i+1==c.n || kind(c.d,x.i+1)!=9 || opening(c.d,x.i+1)!=0f64;
 let pending=x.i+1<c.n && kind(c.d,x.i+1)!=8;
 let pendingWidth=s.width+width;
 let keepsFirst=c.d.profile.hyphenRetreat==HyphenRetreat.FullWidthOrFirst && s.fitBreak==absent();
 let fit=pending && present(c.d.hyphenContexts) && (choose(fits,pendingWidth,s.width)<=c.fit || keepsFirst);
 return next(Scan{..s,lineEnd:text.Cursor{segment:x.i+1,grapheme:0},pending:choose(pending,x.i+1,s.pending),
  pendingWidth:choose(pending,pendingWidth,s.pendingWidth),fitBreak:choose(fit,x.i+1,s.fitBreak),fitPaint:choose(fit,pendingWidth,s.fitPaint)});
}
fn pending_break(c:Config,x:Segment,s:Scan,first:Bool)->Scan {
 let pending=x.breakAfter && (x.i+1==c.n || (c.d.base.flags.at_or(x.i+1,0)&32)==0);
 let width=choose(x.hangs,s.hangStart,choose(x.kind==5,s.width,choose(first,s.width-x.advance,s.width-x.advance-s.trim)));
 let s=Scan{..s,pending:choose(pending,x.i+1,s.pending),pendingWidth:choose(pending,width,s.pendingWidth)};
 let fit=present(c.d.hyphenContexts) && x.breakAfter && s.pendingWidth+room(c.d,s.pending,c.reserved)<=c.fit;
 return Scan{..s,fitBreak:choose(fit,s.pending,s.fitBreak),fitPaint:choose(fit,s.pendingWidth,s.fitPaint)};
}
record Fill { state:Scan, grapheme:u32, done:Bool, }
fn fill_step(c:Config,x:Segment,fillStart:u32,fillSpacing:f64,xs:List<f64>,f:Fill)->Fill {
 let g=f.grapheme;let s=f.state;let width=xs.at_or(g,0f64);
 if !s.content {
  let extras=c.d.base.graphemeStartExtras.fold(fn(es)=>es.at_or(x.i,None),fn(u)=>None);
  let width=extras.fold(fn(es)=>width+es.at_or(g,0f64),fn(u)=>width);
  let extra=choose(g>0,c.d.base.insideExtras,c.d.base.fillExtras);
  let width=extra.fold(fn(es)=>width+es.at_or(x.i,0f64),fn(u)=>width);
  return Fill{state:Scan{..s,content:true,width:width,lineEnd:text.Cursor{segment:x.i,grapheme:g+1}},grapheme:g+1,done:false};
 }
 let candidate=s.width+(width+choose(g>fillStart,c.d.letterSpacing,fillSpacing));
 if candidate+c.d.letterSpacing>c.fit {return Fill{..f,state:Scan{..s,decided:true},done:true};}
 return Fill{state:Scan{..s,width:candidate,lineEnd:text.Cursor{segment:x.i,grapheme:g+1}},grapheme:g+1,done:false};
}
fn fill(c:Config,x:Segment,s:Scan,start:u32,spacing:f64)->Scan {
 let xs=values(c.d.base.advances.at_or(x.i,None));let n=length(xs);
 let f=repeat_until(n,Fill{state:s,grapheme:start,done:false},fn(f)=>f.done || f.grapheme>=n,
  fn(i)=>fn(f)=>fill_step(c,x,start,spacing,xs,f));
 let s=f.state;
 if s.decided {return s;}
 let completed=s.content && s.lineEnd.segment==x.i && s.lineEnd.grapheme==n;
 return next(Scan{..s,lineEnd:choose(completed,text.Cursor{segment:x.i+1,grapheme:0},s.lineEnd)});
}
fn admit_first(c:Config,x:Segment,s:Scan,startExtra:f64,startTrim:f64)->Scan {
 let trimmed=choose(x.fitAdvance+startExtra>c.fit && x.kind!=9,startTrim,0f64);
 let halted=trimmed!=0f64 && halt(c.d,x.i);
 let width=x.width+startExtra;
 let s=Scan{..s,content:true,lineEnd:text.Cursor{segment:x.i+1,grapheme:0},width:choose(halted,width-trimmed,width),
  trim:choose(halted,0f64,trimmed),hangStart:choose(x.hangs,s.hangStart+startExtra,s.hangStart)};
 return next(pending_break(c,x,s,true));
}
fn first(c:Config,x:Segment,s:Scan)->Scan {
 if x.startG>0 {return fill(c,x,s,x.startG,0f64);}
 let extra=scalar(c.d.base.startExtras,x.i);
 let overflowTrim=scalar(c.d.base.overflowTrims,x.i);
 let trim=choose(present(c.d.base.overflowTrims) && x.fitAdvance+extra-overflowTrim<=c.fit,overflowTrim,x.endTrim);
 if x.fitAdvance+extra-trim>c.fit && present(c.d.base.advances.at_or(x.i,None)) && !x.hangs {return fill(c,x,s,0,0f64);}
 return admit_first(c,x,s,extra,trim);
}
fn place_empty(c:Config,x:Segment,s:Scan,newFit:f64)->Bool {
 return c.d.items.fold(fn(items)=>choose(present(items.emptyObjectSpaces) && x.kind==9 && x.width==0f64 && newFit>c.fit,
  choose(s.hangEnd==x.i,s.hangStart,s.width)<=c.fit ||
   !((scalar(items.emptyObjectSpaces,x.i)>=0f64 && choose(s.hangEnd==x.i,s.hangStart,s.width)-scalar(items.emptyObjectSpaces,x.i)>c.fit) ||
     items.emptyObjectReturns.fold(fn(xs)=>xs.at_or(x.i,0),fn(u)=>0)==1),false),fn(u)=>false);
}
fn admitted(c:Config,start:text.Cursor,x:Segment,s:Scan,newFit:f64)->Scan {
 let pending=(x.flags&64)!=0 && !x.breakAfter && s.pending!=x.i;
 let s=Scan{..s,pending:choose(pending,x.i,s.pending),pendingWidth:choose(pending,s.width,s.pendingWidth)};
 let reserves=c.d.profile.hyphenRetreat==HyphenRetreat.ReducedWidth;
 let fit=present(c.d.hyphenContexts) && !x.breakAfter && (x.flags&32)==0 && x.i>start.segment && !breaks_after(kind(c.d,x.i-1)) &&
  (!reserves || s.width+room(c.d,x.i,c.d.hyphenWidth)<=c.fit);
 let s=Scan{..s,fitBreak:choose(fit,x.i,s.fitBreak),fitPaint:choose(fit,s.width,s.fitPaint)};
 let halted=newFit>c.fit && halt(c.d,x.i);
 let width=choose(halted,s.width+(x.advance-x.endTrim),s.width+x.advance);
 let trim=choose(halted,0f64,choose(x.fitAdvance!=0f64 && !x.hangs,choose(newFit>c.fit && x.kind!=9,x.endTrim,0f64),s.trim));
 return next(pending_break(c,x,Scan{..s,width:width,trim:trim,lineEnd:text.Cursor{segment:x.i+1,grapheme:0}},false));
}
fn retreat_object(c:Config,start:text.Cursor,x:Segment,s:Scan)->Option<Scan> {
 let before=x.i-1;let flags=c.d.base.flags.at_or(before,0);let k=flags&15;
 let spaces=choose(k==4,c.d.base.advances.at_or(before,None),None);let count=length(values(spaces));
 let space=values(spaces).at_or(0,0f64);
 let moved=choose(c.d.profile.hardBreakRetreat!=HardBreakRetreat.Fit || s.width<=c.fit,1f64,
  choose(space>0f64,minimum(f64_from_u32(count),ceil((s.width-c.fit)/space)),f64_from_u32(count)));
 let moved=u32_from_f64(moved);
 let contentStart=choose(opening(c.d,start.segment)!=0f64,start.segment+1,start.segment);
 let take=present(spaces) && moved.fold(fn(m)=>before>contentStart || (m<=count && count-m>start.grapheme),fn(u)=>false);
 if take {return Some(stop(s,before,count-moved.fold(fn(m)=>m,fn(u)=>0),s.hangStart));}
 let advances=choose(k==0 || k==7,c.d.base.advances.at_or(before,None),None);let n=length(values(advances));
 let spacing=choose((flags&16)!=0,c.d.letterSpacing,0f64);
 if present(advances) && (before>start.segment || n-1>start.grapheme) {
  return Some(stop(s,before,n-1,s.width-values(advances).at_or(n-1,0f64)-spacing));
 }
 if !present(advances) && (k==0 || k==7) && before>start.segment {
  return Some(stop(s,before,0,s.width-c.d.base.widths.at_or(before,0f64)-spacing));
 }
 if present(spaces) || (k!=4 && k!=5) {
  return Some(next(Scan{..s,width:s.width+x.advance,lineEnd:text.Cursor{segment:x.i+1,grapheme:0},trim:0f64}));
 }
 return None;
}
fn overflow_unbroken(c:Config,start:text.Cursor,x:Segment,s:Scan,newFit:f64)->Scan {
 if present(c.d.base.overflowTrims) && newFit-scalar(c.d.base.overflowTrims,x.i)<=c.fit {
  let trim=scalar(c.d.base.overflowTrims,x.i);let width=s.width+x.advance;let halted=halt(c.d,x.i);
  return next(Scan{..s,width:choose(halted,width-trim,width),trim:choose(halted,0f64,trim),lineEnd:text.Cursor{segment:x.i+1,grapheme:0}});
 }
 let retreat=x.kind==9 && c.d.profile.hardBreakRetreat!=HardBreakRetreat.Item && x.i+1<c.n && kind(c.d,x.i+1)==8;
 let changed=choose(retreat,retreat_object(c,start,x,s),None);
 return changed.fold(fn(s)=>s,fn(u)=>choose(!present(c.d.base.advances.at_or(x.i,None)),
  Scan{..s,decided:true,returnsHyphen:true},fill(c,x,s,0,x.leading)));
}
fn overflow(c:Config,start:text.Cursor,x:Segment,s:Scan,newFit:f64)->Scan {
 let content=s.width-s.trim;
 if x.breakAfter && (x.hangs || x.kind!=5) && (content<=c.fit || (s.pending==absent() && (x.kind==1 || x.kind==2)) ||
  (x.kind==2 && kind(c.d,x.i-1)==9)) {
  return stop(Scan{..s,width:s.width+x.advance},x.i+1,0,choose(x.hangs,s.hangStart,content));
 }
 if x.kind==5 && !x.hangs && s.pending==absent() {return stop(s,x.i,0,choose(s.hangEnd==x.i && x.i>start.segment,s.hangStart,content));}
 let unbroken=(x.flags&32)!=0;
 let openingFit=choose(c.d.profile.openingFit==OpeningFit.Start,
  s.hangStart-s.hangEdges/2f64<=c.fit && s.width-s.hangEdges/2f64>c.fit,
  c.d.profile.openingFit==OpeningFit.Placed && s.hangStart-s.hangEdges+x.width-x.endTrim<=c.fit);
 if x.kind==9 && unbroken && s.hangEnd==x.i && openingFit {
  return next(Scan{..s,hangEnd:x.i+1,hangStart:s.hangStart+x.width,hangEdges:s.hangEdges+x.width,width:s.width+x.advance,
   lineEnd:text.Cursor{segment:x.i+1,grapheme:0}});
 }
 let s=Scan{..s,lineEnd:choose(unbroken && s.pending!=absent(),text.Cursor{segment:s.pending,grapheme:0},s.lineEnd)};
 if !unbroken || s.pending!=absent() {return Scan{..s,decided:true,returnsHyphen:true};}
 return overflow_unbroken(c,start,x,s,newFit);
}
fn with_content(c:Config,start:text.Cursor,x:Segment,s:Scan)->Scan {
 let newFit=choose(x.hangs,s.hangStart-s.hangEdges,s.width+x.fitAdvance);
 let inline=c.d.items.fold(fn(items)=>true,fn(u)=>false);
 let narrows=x.fitAdvance<0f64 && s.width-s.trim>c.fit;
 let overflows=(newFit-x.endTrim>c.fit || (inline && narrows)) && !(inline && x.hangs && s.hangStays) && !place_empty(c,x,s,newFit);
 let hanging=inline && c.d.profile.hangsSpacesPerTextFrame && !overflows && s.hangEnd==x.i && x.kind==9 && x.width==0f64;
 let s=Scan{..s,hangEnd:choose(hanging,x.i+1,s.hangEnd),hangStart:choose(hanging,maximum(s.hangStart,minimum(s.width+x.advance,c.available)),s.hangStart)};
 return choose(overflows,overflow(c,start,x,s,newFit),admitted(c,start,x,s,newFit));
}
fn scan_step(c:Config,start:text.Cursor,s:Scan)->Scan {
 if s.i>=c.n {return end_of_source(s,c.n);}
 if kind(c.d,s.i)==8 {return end_of_source(s,s.i+1);}
 let x=segment(c,start,s);
 let changes=c.d.letterSpacing!=0f64 && (x.spaced || x.kind==7 || x.kind==5 || x.kind==9 || opening(c.d,x.i)!=0f64);
 let s=Scan{..s,afterControl:choose(changes,!x.spaced,s.afterControl),zeroPrefix:choose(x.kind!=2 && x.kind!=6,false,s.zeroPrefix)};
 if x.kind==3 && x.startG==0 {return soft_hyphen(c,start,x,s);}
 let s=hang(c,start,x,s);
 if !s.content && x.kind==6 && !c.d.profile.zeroWidthGlueTakesLine {
  return next(Scan{..s,lineEnd:text.Cursor{segment:x.i+1,grapheme:0}});
 }
 return choose(!s.content,first(c,x,s),with_content(c,start,x,s));
}
fn returns_hyphen(c:Config,start:u32,end:u32,width:f64)->Bool {
 if end==0 || end-1<start || kind(c.d,end-1)!=3 || width<=c.fit {return false;}
 let last=choose(c.d.profile.hyphenRetreat==HyphenRetreat.FullWidth,end,end-1);
 let narrowing=repeat_until(last-start,0f64,fn(s)=>false,fn(i)=>fn(s)=>s+scalar(c.d.hyphenContexts,start+i));
 return narrowing<width-c.fit;
}
record Terminal { width:f64, done:Bool, }
fn terminal_step(c:Config,start:text.Cursor,end:text.Cursor,j:u32,s:Terminal)->Terminal {
 let i=end.segment-1-j;let flags=c.d.base.flags.at_or(i,0);let k=flags&15;
 let skip=k==1 || (k!=7 && k!=5 && (flags&16)==0 && k!=9 && opening(c.d,i)==0f64);
 if skip {return s;}
 return Terminal{width:choose(i==start.segment && start.grapheme>0,c.d.letterSpacing,choose((flags&16)!=0,c.d.letterSpacing,0f64)),done:true};
}
fn terminal(c:Config,start:text.Cursor,end:text.Cursor)->f64 {
 if c.d.letterSpacing==0f64 {return 0f64;}
 if end.grapheme>0 {return choose((c.d.base.flags.at_or(end.segment,0)&16)!=0,c.d.letterSpacing,0f64);}
 if end.segment>0 && end.segment<c.n && kind(c.d,end.segment-1)==3 {return 0f64;}
 if end.segment>start.segment && end.segment<c.n && kind(c.d,end.segment)!=8 && hangs_kind(c.d,kind(c.d,end.segment-1)) {return 0f64;}
 let n=choose(end.segment>=start.segment,end.segment-start.segment,0);
 let s=repeat_until(n,Terminal{width:0f64,done:false},fn(s)=>s.done,fn(i)=>fn(s)=>terminal_step(c,start,end,i,s));
 return s.width;
}
fn initial(start:text.Cursor)->Scan {
 return Scan{i:start.segment,width:0f64,content:false,lineEnd:start,pending:absent(),pendingWidth:0f64,fitBreak:absent(),fitPaint:0f64,
  hangEnd:absent(),hangStart:0f64,hangStays:false,hangEdges:0f64,trim:0f64,zeroPrefix:true,afterControl:false,
  end:absent(),endG:0,endWidth:0f64,returnsHyphen:false,decided:false};
}
fn finish_line(c:Config,start:text.Cursor,s:Scan)->text.Line {
 let returns=s.returnsHyphen && s.fitBreak!=absent() && s.pending==s.lineEnd.segment && s.lineEnd.grapheme==0 &&
  returns_hyphen(c,start.segment,s.lineEnd.segment,s.pendingWidth);
 let implicit=s.end==absent();
 let end=choose(returns,text.Cursor{segment:s.fitBreak,grapheme:0},choose(implicit,s.lineEnd,text.Cursor{segment:s.end,grapheme:s.endG}));
 let endWidth=choose(returns,s.fitPaint,choose(implicit,
  choose(s.pending==s.lineEnd.segment && s.lineEnd.grapheme==0,s.pendingWidth,
   choose(c.d.items.fold(fn(items)=>true,fn(u)=>false) && s.hangEnd==s.lineEnd.segment && s.lineEnd.grapheme==0,s.hangStart,s.width-s.trim)),s.endWidth));
 let hangs=end.grapheme==0 && s.hangEnd!=absent() && (end.segment==s.hangEnd || end.segment==s.hangEnd+1) &&
  (s.hangEnd==c.n || kind(c.d,s.hangEnd)==8);
 let paint=choose(hangs,s.width-s.trim,endWidth)+terminal(c,start,end);
 return text.Line{start:start,end:end,width:choose(hangs,maximum(s.hangStart,minimum(paint,c.available)),paint)};
}
fn step(c:Config,start:text.Cursor,budget:u32)->Result<Option<text.Line>,String> {
 if kind(c.d,start.segment)==8 {return Ok(Some(text.Line{start:start,end:text.Cursor{segment:start.segment+1,grapheme:0},width:scalar(c.d.base.startExtras,start.segment)}));}
 let s=repeat_until(budget+1,initial(start),fn(s)=>s.decided,fn(i)=>fn(s)=>scan_step(c,start,s));
 if !s.decided {return Err("complex line work budget exhausted");}
 if !s.content {return Ok(None);}
 let line=finish_line(c,start,s);
 if line.end.segment<start.segment || (line.end.segment==start.segment && line.end.grapheme<=start.grapheme) {return Err("complex line did not advance");}
 return Ok(Some(line));
}
fn line_from(p:Prepared,cursor:text.Cursor,width:f64)->Result<Option<text.Line>,String>
 requires(valid(p),"invalid complex prepared text") {
 let n=length(p.data.base.widths);
 if cursor.segment>n || (cursor.segment==n && cursor.grapheme>0) ||
  (cursor.grapheme>0 && !p.data.base.advances.at_or(cursor.segment,None).fold(fn(xs)=>cursor.grapheme<length(xs),fn(u)=>false)) {return Err("invalid complex line cursor");}
 return normalize(p.data,cursor).fold(fn(start)=>step(config(p.data,width),start,p.budget),fn(u)=>Ok(None));
}
record Walk { cursor:text.Cursor, stats:text.Stats, done:Bool, error:Option<String>, }
fn walk_step(c:Config,budget:u32,w:Walk)->Walk {
 return normalize(c.d,w.cursor).fold(fn(start)=>step(c,start,budget).fold(fn(line)=>line.fold(
  fn(line)=>Walk{..w,cursor:line.end,stats:text.Stats{lineCount:w.stats.lineCount+1,maxLineWidth:choose(line.width>w.stats.maxLineWidth,line.width,w.stats.maxLineWidth)}},
  fn(u)=>Walk{..w,done:true}),fn(error)=>Walk{..w,done:true,error:Some(error)}),fn(u)=>Walk{..w,done:true});
}
fn stats(p:Prepared,width:f64)->Result<text.Stats,String>
 requires(valid(p),"invalid complex prepared text") {
 let c=config(p.data,width);
 let w=repeat_until(p.budget+1,Walk{cursor:text.Cursor{segment:0,grapheme:0},stats:text.Stats{lineCount:0,maxLineWidth:0f64},done:false,error:None},
  fn(w)=>w.done,fn(i)=>fn(w)=>walk_step(c,p.budget,w));
 if !w.done {return Err("complex paragraph work budget exhausted");}
 return w.error.fold(fn(error)=>Err(error),fn(u)=>Ok(w.stats));
}
record Ranges { cursor:text.Cursor, lines:Buffer<text.Line>, done:Bool, error:Option<String>, }
fn ranges_step(c:Config,budget:u32,w:Ranges)->Ranges {
 return normalize(c.d,w.cursor).fold(fn(start)=>step(c,start,budget).fold(fn(line)=>line.fold(
  fn(line)=>Ranges{cursor:line.end,lines:w.lines.push(line),done:false,error:None},
  fn(u)=>Ranges{..w,done:true}),fn(error)=>Ranges{..w,done:true,error:Some(error)}),fn(u)=>Ranges{..w,done:true});
}
fn lines(p:Prepared,width:f64)->Result<List<text.Line>,String>
 requires(valid(p),"invalid complex prepared text") {
 let c=config(p.data,width);
 let w=repeat_until(p.budget+1,Ranges{cursor:text.Cursor{segment:0,grapheme:0},lines:Buffer.empty(),done:false,error:None},
  fn(w)=>w.done,fn(i)=>fn(w)=>ranges_step(c,p.budget,w));
 if !w.done {return Err("complex paragraph work budget exhausted");}
 if w.error.fold(fn(error)=>true,fn(u)=>false) {return Err(w.error.fold(fn(error)=>error,fn(u)=>"complex layout error"));}
 return Ok(w.lines.freeze());
}
fn line_count(p:Prepared,width:f64)->Result<u32,String> {return stats(p,width).map(fn(stats)=>stats.lineCount);}
fn layout(p:Prepared,width:f64,lineHeight:f64)->Result<text.Layout,String> {
 return line_count(p,width).map(fn(n)=>text.Layout{lineCount:n,height:f64_from_u32(n)*lineHeight});
}
