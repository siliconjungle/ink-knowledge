module ink.knowledge.prepared_text;
// Binary64 prepared line geometry. Ported from Pretext 0a27bbe0, MIT.
// Copyright (c) 2026 Pretext contributors. See notices/pretext-LICENSE.txt.
// This module covers the simple walker, including emergency grapheme breaks,
// line-edge shaping corrections and rich-inline inside/fill extras. Segmentation
// and measurement are external inputs; complex break kinds are not approximated.
record Data {
 widths:List<f64>, flags:List<u32>, advances:List<Option<List<f64>>>,
 startExtras:Option<List<f64>>, graphemeStartExtras:Option<List<Option<List<f64>>>>,
 endTrims:Option<List<f64>>, overflowTrims:Option<List<f64>>,
 insideExtras:Option<List<f64>>, fillExtras:Option<List<f64>>,
}
abstract record Prepared { data:Data, epsilon:f64, budget:u32, }
record Cursor { segment:u32, grapheme:u32, }
record Line { width:f64, start:Cursor, end:Cursor, }
record Stats { lineCount:u32, maxLineWidth:f64, }
record Layout { lineCount:u32, height:f64, }

fn scalar(xs:Option<List<f64>>,i:u32)->f64 {return xs.fold(fn(xs)=>xs.at_or(i,0f64),fn(u)=>0f64);}
fn extra(d:Data,i:u32)->Option<List<f64>> {return d.graphemeStartExtras.fold(fn(xs)=>xs.at_or(i,None),fn(u)=>None);}
fn kind(d:Data,i:u32)->u32 {return d.flags.at_or(i,0)&15;}
fn consumes(d:Data,i:u32,atStart:Bool)->Bool {return kind(d,i)==1 || (kind(d,i)==2 && !atStart);}
fn breaks_after(d:Data,i:u32)->Bool {return kind(d,i)==1 || kind(d,i)==2;}
fn finite(xs:List<f64>)->Bool {return foldl(xs,true,fn(x)=>fn(ok)=>ok && is_finite(x));}
fn sized(xs:Option<List<f64>>,n:u32)->Bool {return xs.fold(fn(xs)=>count(xs)<=1000000 && length(xs)==n && finite(xs),fn(u)=>true);}
record Shape { valid:Bool, budget:u32, index:u32, }
fn shape_step(d:Data,maximum:u32,advance:Option<List<f64>>,s:Shape)->Shape {
 let i=s.index;let flags=d.flags.at_or(i,256);let k=flags&15;
 let size=advance.fold(fn(xs)=>length(xs),fn(u)=>0);
 let valid=s.valid && flags<=255 && k<=2 && (flags&32)==0 &&
     advance.fold(fn(xs)=>count(xs)>0 && count(xs)<=1000000 && length(xs)<=maximum && finite(xs),fn(u)=>true) &&
     extra(d,i).fold(fn(xs)=>advance.fold(fn(a)=>count(xs)==count(a) && finite(xs),fn(u)=>false),fn(u)=>true);
 let fits=size<=maximum-s.budget;
 return Shape{valid:valid && fits,budget:choose(fits,s.budget+size,s.budget),index:i+1};
}
fn checked_budget(d:Data,epsilon:f64,maximum:u32)->Option<u32> {
 if maximum==0 || maximum>1000000 || count(d.widths)>1000000 || length(d.widths)>maximum || !finite(d.widths) ||
    !is_finite(epsilon) || epsilon<0f64 {return None;}
 let n=length(d.widths);
 if count(d.flags)>1000000 || length(d.flags)!=n || count(d.advances)>1000000 || length(d.advances)!=n || !sized(d.startExtras,n) ||
    !sized(d.endTrims,n) || !sized(d.overflowTrims,n) || !sized(d.insideExtras,n) ||
    !sized(d.fillExtras,n) || !d.graphemeStartExtras.fold(fn(xs)=>count(xs)<=1000000 && length(xs)==n,fn(u)=>true) {return None;}
 let s=foldl(d.advances,Shape{valid:true,budget:n,index:0},fn(a)=>fn(s)=>shape_step(d,maximum,a,s));
 return choose(s.valid,Some(s.budget),None);
}
fn prepare(d:Data,epsilon:f64,maximum:u32)->Result<Prepared,String> {
 return checked_budget(d,epsilon,maximum).fold(fn(b)=>Ok(Prepared{data:d,epsilon:epsilon,budget:b}),fn(u)=>Err("invalid simple prepared text"));
}
fn valid(p:Prepared)->Bool {return checked_budget(p.data,p.epsilon,1000000).fold(fn(b)=>b==p.budget,fn(u)=>false);}
// Public paragraph APIs normalize NaN to an unbounded width, like Pretext.
fn normalize_width(width:f64)->f64 {return choose(is_nan(width),f64_from_bits(9218868437227405312),width);}
fn limit(p:Prepared,width:f64)->f64 {return choose(width>0f64,width,0f64)+p.epsilon;}

record Start { cursor:Cursor, done:Bool, }
fn normalize(d:Data,c:Cursor)->Cursor {
 let n=length(d.widths);let atStart=c.segment==0;
 let s=repeat_until(n,Start{cursor:c,done:c.grapheme>0 || c.segment>=n},fn(s)=>s.done,fn(i)=>fn(s)=>
   choose(consumes(d,s.cursor.segment,atStart),
     Start{cursor:Cursor{segment:s.cursor.segment+1,grapheme:0},done:s.cursor.segment+1>=n},
     Start{cursor:s.cursor,done:true}));
 return s.cursor;
}
record Graphemes { index:u32, width:f64, done:Bool, }
fn fill_graphemes(xs:List<f64>,start:u32,width:f64,fit:f64)->Graphemes {
 return repeat_until(length(xs),Graphemes{index:start,width:width,done:false},fn(s)=>s.done || s.index>=length(xs),fn(i)=>fn(s)=>
   choose(s.width+xs.at_or(s.index,0f64)>fit,
     Graphemes{..s,done:true},
     Graphemes{index:s.index+1,width:s.width+xs.at_or(s.index,0f64),done:false}));
}
record Tail { index:u32, width:f64, trimmed:f64, end:Cursor, result:f64, done:Bool, }
fn tail_step(d:Data,fit:f64,s:Tail)->Tail {
 let i=s.index;let w=d.widths.at_or(i,0f64);let trim=scalar(d.endTrims,i);
 if s.width+w-trim>fit {
  let hangs=breaks_after(d,i);
  let result=choose(!hangs && breaks_after(d,i-1),s.width-d.widths.at_or(i-1,0f64),s.width-s.trimmed);
  return Tail{..s,end:Cursor{segment:choose(hangs,i+1,i),grapheme:0},result:result,done:true};
 }
 let width=s.width+w;
 return Tail{..s,index:i+1,width:width,trimmed:choose(width>fit,trim,0f64)};
}
fn step(p:Prepared,c:Cursor,width:f64)->Line {
 let d=p.data;let fit=limit(p,width);let n=length(d.widths);let start=c.segment;
 let advance=d.advances.at_or(start,None);
 let startW=d.startExtras.fold(fn(es)=>d.widths.at_or(start,0f64)+es.at_or(start,0f64),fn(u)=>d.widths.at_or(start,0f64));
 let endTrim=scalar(d.endTrims,start);
 let startTrim=d.overflowTrims.fold(fn(xs)=>choose(startW-xs.at_or(start,0f64)<=fit,xs.at_or(start,0f64),endTrim),fn(u)=>endTrim);
 let split=c.grapheme>0 || (startW-startTrim>fit && advance.fold(fn(xs)=>true,fn(u)=>false));
 let xs=advance.fold(fn(xs)=>xs,fn(u)=>[]);
 let initial=extra(d,start).fold(fn(es)=>xs.at_or(c.grapheme,0f64)+es.at_or(c.grapheme,0f64),fn(u)=>xs.at_or(c.grapheme,0f64));
 let initial=choose(c.grapheme>0,d.insideExtras,d.fillExtras).fold(fn(es)=>initial+es.at_or(start,0f64),fn(u)=>initial);
 let g=choose(split,fill_graphemes(xs,c.grapheme+1,initial,fit),Graphemes{index:length(xs),width:startW,done:false});
 if split && g.index<length(xs) {return Line{width:g.width,start:c,end:Cursor{segment:start,grapheme:g.index}};}
 let trimmed=choose(!split && startW>fit,startTrim,0f64);
 let t=repeat_until(n,Tail{index:start+1,width:g.width,trimmed:trimmed,end:Cursor{segment:n,grapheme:0},result:0f64,done:false},fn(t)=>t.done || t.index>=n,fn(i)=>fn(t)=>tail_step(d,fit,t));
 return Line{width:choose(t.done,t.result,t.width-t.trimmed),start:c,end:t.end};
}
fn line_from(p:Prepared,c:Cursor,width:f64)->Result<Option<Line>,String>
 requires(valid(p),"invalid prepared text") {
 let n=length(p.data.widths);
 if c.segment>n || (c.segment==n && c.grapheme>0) ||
    (c.grapheme>0 && !p.data.advances.at_or(c.segment,None).fold(fn(xs)=>c.grapheme<length(xs),fn(u)=>false)) {return Err("invalid line cursor");}
 let start=normalize(p.data,c);
 if start.segment>=n {return Ok(None);}
 return Ok(Some(step(p,start,normalize_width(width))));
}

record Walk { cursor:Cursor, stats:Stats, done:Bool, }
fn walk_step(p:Prepared,width:f64,w:Walk)->Walk {
 let start=normalize(p.data,w.cursor);
 if start.segment>=length(p.data.widths) {return Walk{..w,done:true};}
 let line=step(p,start,width);
 return Walk{cursor:line.end,stats:Stats{lineCount:w.stats.lineCount+1,maxLineWidth:choose(line.width>w.stats.maxLineWidth,line.width,w.stats.maxLineWidth)},done:false};
}
fn walk(p:Prepared,width:f64)->Stats {
 let w=repeat_until(p.budget+1,Walk{cursor:Cursor{segment:0,grapheme:0},stats:Stats{lineCount:0,maxLineWidth:0f64},done:false},fn(w)=>w.done,fn(i)=>fn(w)=>walk_step(p,width,w));
 return w.stats;
}
fn stats(p:Prepared,width:f64)->Result<Stats,String>
 requires(valid(p),"invalid prepared text") {
 return Ok(walk(p,normalize_width(width)));
}
record Ranges { cursor:Cursor, lines:Buffer<Line>, done:Bool, }
fn ranges_step(p:Prepared,width:f64,w:Ranges)->Ranges {
 let start=normalize(p.data,w.cursor);
 if start.segment>=length(p.data.widths) {return Ranges{..w,done:true};}
 let line=step(p,start,width);
 return Ranges{cursor:line.end,lines:w.lines.push(line),done:false};
}
fn lines(p:Prepared,width:f64)->Result<List<Line>,String>
 requires(valid(p),"invalid prepared text") {
 let w=repeat_until(p.budget+1,Ranges{cursor:Cursor{segment:0,grapheme:0},lines:Buffer.empty(),done:false},fn(w)=>w.done,fn(i)=>fn(w)=>ranges_step(p,normalize_width(width),w));
 return Ok(w.lines.freeze());
}

record Count { lines:u32, width:f64, content:Bool, }
record CountGraphemes { count:Count, index:u32, }
fn count_fill(xs:List<f64>,start:u32,width:f64,fit:f64)->Graphemes {
 return repeat_until(length(xs),Graphemes{index:start,width:width,done:false},fn(s)=>s.done || s.index>=length(xs),fn(i)=>fn(s)=>
   choose(s.width+xs.at_or(s.index,0f64)<=fit,
     Graphemes{index:s.index+1,width:s.width+xs.at_or(s.index,0f64),done:false},
     Graphemes{..s,done:true}));
}
fn count_graphemes(xs:List<f64>,es:Option<List<f64>>,fit:f64,s:CountGraphemes)->CountGraphemes {
 let width=s.count.width+es.fold(fn(es)=>es.at_or(s.index,0f64),fn(u)=>0f64);
 let width=width+xs.at_or(s.index,0f64);
 let g=count_fill(xs,s.index+1,width,fit);
 if g.index<length(xs) {return CountGraphemes{count:Count{lines:s.count.lines+1,width:0f64,content:false},index:g.index};}
 return CountGraphemes{count:Count{lines:s.count.lines,width:g.width,content:true},index:g.index};
}
fn count_step(d:Data,fit:f64,i:u32,s:Count)->Count {
 let k=kind(d,i);let w=d.widths.at_or(i,0f64);let trim=scalar(d.endTrims,i);
 if s.content && s.width+w-trim<=fit {return Count{..s,width:s.width+w};}
 let overflow=s.content;
 let s=choose(overflow,Count{lines:s.lines+1,width:0f64,content:false},s);
 if (overflow && k!=0) || (!overflow && (k==1 || (k==2 && i>0))) {return s;}
 let startW=d.startExtras.fold(fn(es)=>w+es.at_or(i,0f64),fn(u)=>w);let advances=d.advances.at_or(i,None);
 if startW-trim<=fit || advances.fold(fn(xs)=>false,fn(u)=>true) {return Count{..s,width:s.width+startW,content:true};}
 let xs=advances.fold(fn(xs)=>xs,fn(u)=>[]);
 let g=repeat_until(length(xs),CountGraphemes{count:s,index:0},fn(g)=>g.index>=length(xs),fn(j)=>fn(g)=>count_graphemes(xs,extra(d,i),fit,g));
 return g.count;
}
fn line_count(p:Prepared,width:f64)->Result<u32,String>
 requires(valid(p),"invalid prepared text") {
 let width=normalize_width(width);
 // Pretext uses the geometry walker where overflow-specific trims are present.
 if p.data.overflowTrims.fold(fn(xs)=>true,fn(u)=>false) {return Ok(walk(p,width).lineCount);}
 let c=repeat_until(length(p.data.widths),Count{lines:0,width:0f64,content:false},fn(c)=>false,fn(i)=>fn(c)=>count_step(p.data,limit(p,width),i,c));
 return Ok(c.lines+choose(c.content,1,0));
}
fn layout(p:Prepared,width:f64,lineHeight:f64)->Result<Layout,String> {
 return line_count(p,width).map(fn(n)=>Layout{lineCount:n,height:f64_from_u32(n)*lineHeight});
}
