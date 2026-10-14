// Optional untimed diagnostic acquisition, never production or proof authority.
import fs from 'node:fs';
import crypto from 'node:crypto';
import {pathToFileURL} from 'node:url';
const [input, output, receipt, parserPath] = process.argv.slice(2);
if (!input || !output || !receipt || !parserPath) throw Error('input output receipt parser required');
const raw=fs.readFileSync(input);if(raw.length>16_000_000)throw Error('diagnostic source byte budget');const source=new TextDecoder('utf-8',{fatal:true}).decode(raw);
const {parse}=await import(pathToFileURL(parserPath));
const ast=parse(source,{ecmaVersion:'latest',sourceType:'module'});
const pending=[[ast,0]];let nodes=0;while(pending.length){const [x,d]=pending.pop();if(!x||typeof x!=='object')continue;if(++nodes>200000||d>256)throw Error('diagnostic AST budget');for(const [k,v]of Object.entries(x)){if(['start','end','loc','range'].includes(k))continue;if(Array.isArray(v))for(const c of v)pending.push([c,d+1]);else if(v&&typeof v==='object')pending.push([v,d+1]);}}
const digest=x=>crypto.createHash('sha256').update(x).digest('hex');
const prefix='__ink_work_'+digest(raw).slice(0,16);
if(source.includes(prefix))throw Error('diagnostic name collision');
const sites=[],unknown=[];
const callbacks=new Set(['map','filter','sort','reduce','reduceRight','forEach','some','every','find','findIndex','findLast','findLastIndex']);
const methods=new Set(['slice','set','concat','from','of',...callbacks]);
function site(node,kind){const id=sites.length;sites.push({id,kind,start:node.start,end:node.end,offset_unit:'UTF16',source_sha256:digest(source.slice(node.start,node.end))});return id}
function children(node){
 const result=[],seen=new Set();
 for(const [key,value]of Object.entries(node)){
  if(['start','end','loc','range'].includes(key))continue;
  for(const child of Array.isArray(value)?value:[value])if(child&&typeof child.type==='string'&&Number.isInteger(child.start)&&Number.isInteger(child.end)){
   const key=child.start+':'+child.end;if(!seen.has(key)){seen.add(key);result.push(child);}
  }
 }
 // Shorthand defaults expose the same identifier as both Property.key and
 // inside AssignmentPattern.value. Render the containing child only once.
 const ordered=result.sort((a,b)=>a.start-b.start||b.end-a.end),outer=[];
 for(const child of ordered)if(!outer.length||child.start>=outer.at(-1).end||child.end>outer.at(-1).end)outer.push(child);
 return outer;
}
function splice(start,end,parts){
 let text='',at=start;
 for(const [child,value]of parts){if(child.start<at||child.end>end)throw Error('overlapping diagnostic AST children');text+=source.slice(at,child.start)+value;at=child.end;}
 return text+source.slice(at,end);
}
function render(node,inFunction=false){
 const inner=inFunction||['FunctionDeclaration','FunctionExpression','ArrowFunctionExpression'].includes(node.type);
 if(inFunction&&node.type==='CallExpression'&&node.callee.type==='MemberExpression'){
  const p=node.callee.property,method=node.callee.computed?(p.type==='Literal'?p.value:null):(p.type==='Identifier'?p.name:null);
  if(methods.has(method)){
   if(node.optional||node.callee.optional||node.callee.object.type==='Super')unknown.push({site:node.start,reason:'optional/super copying call not instrumented'});
   else{
    const id=site(node,'copy_or_allocation_call');
    if(callbacks.has(method)||method==='from')sites[id].callback_site=site(node,'native_callback_iterations');
    const opening=source.indexOf('(',node.callee.end);
    if(opening<0||opening>=node.end)throw Error('call delimiter unavailable');
    // Construct the bound invocation before evaluating the arguments, retaining
    // receiver/getter/argument order and lexical await/yield/this. Recursive
    // rendering keeps instrumentation inside chained receivers and arguments.
    const receiver=render(node.callee.object,inner);
    const args=splice(opening+1,node.end-1,node.arguments.map(a=>[a,render(a,inner)]));
    return `${prefix}_prepare(${id},${JSON.stringify(method)},(${receiver}))(${args})`;
   }
  }
 }
 let kind=null,id=null;
 if(inFunction&&node.type==='ArrayExpression'){kind='allocate';id=site(node,'allocation_events');}
 if(inFunction&&node.type==='NewExpression'){
  kind='construct';id=site(node,'construction');sites[id].constructor_capacity_only=node.arguments.length===0||node.arguments.length===1&&node.arguments[0].type==='Literal'&&typeof node.arguments[0].value==='number';
 }
 const loop=inFunction&&['ForStatement','WhileStatement','DoWhileStatement','ForOfStatement','ForInStatement'].includes(node.type);
 const loopId=loop?site(node,'loop_iterations'):null;
 const parts=children(node).map(child=>{
  let value=render(child,inner);
  if(loop&&child===node.body)value=child.type==='BlockStatement'?value.slice(0,1)+`${prefix}_hit(${loopId});`+value.slice(1):`{${prefix}_hit(${loopId});${value}}`;
  return [child,value];
 });
 const value=splice(node.start,node.end,parts);
 return kind?`${prefix}_${kind}(${id},${value})`:value;
}
const instrumented=render(ast);
const prelude=`
const ${prefix}_sites=${JSON.stringify(sites)};
let ${prefix}_counts=[],${prefix}_unknown=[];
function ${prefix}_hit(i){${prefix}_counts[i]=(${prefix}_counts[i]??0)+1;}
function ${prefix}_allocate(i,x){${prefix}_hit(i);return x;}
function ${prefix}_construct(i,x){if(Array.isArray(x)||ArrayBuffer.isView(x)||x instanceof ArrayBuffer){${prefix}_hit(i);if(ArrayBuffer.isView(x)&&!${prefix}_sites[i].constructor_capacity_only)${prefix}_unknown.push({site:i,components:['copy_bytes'],reason:'typed constructor ingress/copy extent not captured'});}else ${prefix}_unknown.push({site:i,components:['allocation_events'],reason:'constructor allocation behavior unknown'});return x;}
function ${prefix}_prepare(i,name,receiver){const method=receiver[name];return(...args)=>${prefix}_invoke(i,name,receiver,method,args);}
const ${prefix}_typedConstructors=[Int8Array,Uint8Array,Uint8ClampedArray,Int16Array,Uint16Array,Int32Array,Uint32Array,Float32Array,Float64Array,BigInt64Array,BigUint64Array];
function ${prefix}_invoke(i,name,receiver,method,args){
 // Invoke the original native operation once. A diagnostic callback records
 // actual visits (including sparse-array skipped entries), preserving original
 // this/arguments and exception order. Opaque custom methods are left alone.
 const factory=name==='from'||name==='of';
 const standardFactory=factory&&(receiver===Array||${prefix}_typedConstructors.includes(receiver))&&method===(receiver===Array?Array[name]:Object.getPrototypeOf(Uint8Array)[name]);
 const proto=Object.getPrototypeOf(receiver);
 const standard=standardFactory||(Array.isArray(receiver)?proto===Array.prototype&&method===Array.prototype[name]:(ArrayBuffer.isView(receiver)&&typeof receiver.BYTES_PER_ELEMENT==='number'?method===Object.getPrototypeOf(Uint8Array.prototype)[name]:receiver instanceof ArrayBuffer&&method===ArrayBuffer.prototype[name]));
 const callbackIndex=name==='from'?1:0,callbackSite=${prefix}_sites[i].callback_site;
 if(standard&&callbackSite!==undefined&&typeof args[callbackIndex]==='function'){const callback=args[callbackIndex];args[callbackIndex]=function(...values){${prefix}_hit(callbackSite);return Reflect.apply(callback,this,values);};}
 else if(standard&&(name==='sort'||factory))${prefix}_unknown.push({site:i,components:['loop_iterations'],reason:'native traversal without an observable callback'});
 const value=Reflect.apply(method,receiver,args);
 if(!standard){${prefix}_unknown.push({site:i,components:['allocation_events','copy_bytes','loop_iterations'],reason:'copy method implementation/carrier unknown'});return value;}
 if(name==='concat')${prefix}_unknown.push({site:i,components:['copy_bytes'],reason:'native concat carrier copy bytes unknown'});
 if(name==='set'){
  if(ArrayBuffer.isView(receiver)&&ArrayBuffer.isView(args[0])&&Object.getPrototypeOf(receiver)===Object.getPrototypeOf(args[0]))${prefix}_copy_bytes+=args[0].byteLength;
  else ${prefix}_unknown.push({site:i,components:['copy_bytes'],reason:'set byte extent or conversion unknown'});
 }else if(['slice','map','filter','concat','from','of'].includes(name)&&(Array.isArray(value)||ArrayBuffer.isView(value)||value instanceof ArrayBuffer)){
  ${prefix}_hit(i);
  if(name==='slice'&&(ArrayBuffer.isView(value)||value instanceof ArrayBuffer))${prefix}_copy_bytes+=value.byteLength;
  else if(name==='slice')${prefix}_unknown.push({site:i,components:['copy_bytes'],reason:'JS Array copy bytes/physical storage unknown'});
  if(name==='from'){
   if(args[1]===undefined&&ArrayBuffer.isView(args[0])&&${prefix}_typedConstructors.includes(receiver)&&Object.getPrototypeOf(args[0])===receiver.prototype)${prefix}_copy_bytes+=args[0].byteLength;
   else ${prefix}_unknown.push({site:i,components:['copy_bytes'],reason:'factory input conversion or JS Array copy extent unknown'});
  }
 }
 return value;
}
let ${prefix}_copy_bytes=0;
export function ${prefix}_reset(){${prefix}_counts=[];${prefix}_unknown=[];${prefix}_copy_bytes=0;}
export function ${prefix}_snapshot(){return {sites:${prefix}_counts.slice(),copy_bytes:${prefix}_copy_bytes,unknown:${prefix}_unknown.slice()};}
`;
// Parse instrumented output before freezing it. Unsupported edits fail closed.
parse(prelude+instrumented,{ecmaVersion:'latest',sourceType:'module'});
fs.writeFileSync(output,prelude+instrumented,{flag:'wx'});
fs.writeFileSync(receipt,JSON.stringify({schema:1,target:'javascript',artifact_sha256:digest(raw),instrumented_sha256:digest(fs.readFileSync(output)),instrumenter_sha256:digest(fs.readFileSync(new URL(import.meta.url))),parser_sha256:digest(fs.readFileSync(parserPath)),prefix,sites,unknown,scope:'Untimed literal emitted-site instrumentation; allocation events are completed carrier constructions, not V8 physical allocator calls; JS Array bytes unknown'},null,2)+'\n',{flag:'wx'});
