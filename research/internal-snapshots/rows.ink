module ink.knowledge.field_snapshots;
record Row{id:u32,x:u32,y:u32,score:u32,flags:u32,}
record InkFieldStored<T>{value:T,}
record InkFieldDelta0{field:u32,value:u32,}
record InkFieldValues0{id:u32,x:u32,}
fn build_fields0(a:Row,b:Row)->Buffer<InkFieldDelta0>{
var out:Buffer<InkFieldDelta0>=Buffer.empty();
if InkFieldStored<u32>{value:a.id}!=InkFieldStored<u32>{value:b.id}{out=out.push(InkFieldDelta0{field:0,value:b.id});}
if InkFieldStored<u32>{value:a.x}!=InkFieldStored<u32>{value:b.x}{out=out.push(InkFieldDelta0{field:1,value:b.x});}
return out;}
fn replay_fields0(a:Row,edits:Buffer<InkFieldDelta0>)->InkFieldValues0{
var v0:u32=a.id;
var v1:u32=a.x;
for edit in edits.freeze(){
if edit.field==0{v0=edit.value;}
if edit.field==1{v1=edit.value;}
}
return InkFieldValues0{id:v0,x:v1,};}
record InkFieldDelta1{field:u32,value:u32,}
record InkFieldValues1{y:u32,score:u32,}
fn build_fields1(a:Row,b:Row)->Buffer<InkFieldDelta1>{
var out:Buffer<InkFieldDelta1>=Buffer.empty();
if InkFieldStored<u32>{value:a.y}!=InkFieldStored<u32>{value:b.y}{out=out.push(InkFieldDelta1{field:2,value:b.y});}
if InkFieldStored<u32>{value:a.score}!=InkFieldStored<u32>{value:b.score}{out=out.push(InkFieldDelta1{field:3,value:b.score});}
return out;}
fn replay_fields1(a:Row,edits:Buffer<InkFieldDelta1>)->InkFieldValues1{
var v2:u32=a.y;
var v3:u32=a.score;
for edit in edits.freeze(){
if edit.field==2{v2=edit.value;}
if edit.field==3{v3=edit.value;}
}
return InkFieldValues1{y:v2,score:v3,};}
record InkFieldDelta2{field:u32,value:u32,}
record InkFieldValues2{flags:u32,}
fn build_fields2(a:Row,b:Row)->Buffer<InkFieldDelta2>{
var out:Buffer<InkFieldDelta2>=Buffer.empty();
if InkFieldStored<u32>{value:a.flags}!=InkFieldStored<u32>{value:b.flags}{out=out.push(InkFieldDelta2{field:4,value:b.flags});}
return out;}
fn replay_fields2(a:Row,edits:Buffer<InkFieldDelta2>)->InkFieldValues2{
var v4:u32=a.flags;
for edit in edits.freeze(){
if edit.field==4{v4=edit.value;}
}
return InkFieldValues2{flags:v4,};}
fn reconcile_fields(before:List<Row>,after:List<Row>)->List<Row>{
if before==after{return before;}
var out:Buffer<Row>=buffer(before).truncate(length(after));var index:u32=0;
for row in after{if index>=length(before){out=out.push(row);}else{
let previous:Row=before.at_or(index,row);
if previous!=row{
let fields0=replay_fields0(previous,build_fields0(previous,row));
let fields1=replay_fields1(previous,build_fields1(previous,row));
let fields2=replay_fields2(previous,build_fields2(previous,row));
out=out.set(index,Row{id:fields0.id,x:fields0.x,y:fields1.y,score:fields1.score,flags:fields2.flags,});
}}index=index+1;}return out.freeze();}
