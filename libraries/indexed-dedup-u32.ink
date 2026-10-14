module ink.knowledge.indexed_dedup;
fn empty_words()->List<u32>{return [];}
fn member(xs:List<u32>,key:u32)->Bool {
 return foldr(xs,false,fn(item,found)=>key==item||found);
}
fn key_index(xs:List<u32>)->Map<u32,Bool> {
 return foldr(xs,Map.empty(),fn(item,index)=>index.set(item,true));
}
record IndexedWords { output:Buffer<u32>, seen:Map<u32,Bool>, }
fn encode_words(xs:List<u32>)->IndexedWords {
 return IndexedWords{output:buffer(xs),seen:key_index(xs)};
}
fn dedup_step(item:u32,output:List<u32>)->List<u32> {
 return choose(member(output,item),output,output.concat([item]));
}
fn indexed_step(item:u32,state:IndexedWords)->IndexedWords {
 return choose(state.seen.contains(item),state,
  IndexedWords{output:state.output.push(item),seen:state.seen.set(item,true)});
}
law index_membership(xs:List<u32>,key:u32) {
 key_index(xs).contains(key)==member(xs,key);
 proof by induction xs {
  nil=>normalize;
  cons(head,tail)=>cases key==head {true=>normalize;false=>normalize;};
 };
}
law index_append_one(xs:List<u32>,key:u32) {
 key_index(xs.concat([key]))==key_index(xs).set(key,true);
 proof by induction xs {
  nil=>normalize;
  cons(head,tail)=>calc {
   _==key_index(tail.concat([key])).set(head,true) by normalize;
   ==key_index(tail).set(key,true).set(head,true) by congruence(hypothesis 0,normalize,normalize);
   ==key_index(tail).set(head,true).set(key,true) by use map_same_value_updates_u32<Bool>(key_index(tail),key,head,true);
   ==_ by normalize;
  };
 };
}
law indexed_step_encoded(item:u32,output:List<u32>) {
 indexed_step(item,encode_words(output))==choose(member(output,item),encode_words(output),
  IndexedWords{output:buffer(output).push(item),seen:key_index(output).set(item,true)});
 proof by calc {
  _==choose(key_index(output).contains(item),encode_words(output),
   IndexedWords{output:buffer(output).push(item),seen:key_index(output).set(item,true)}) by normalize;
  ==_ by congruence(use index_membership(output,item),normalize,normalize);
 };
}
law encoded_dedup_step(item:u32,output:List<u32>) {
 encode_words(dedup_step(item,output))==indexed_step(item,encode_words(output));
 proof by calc {
  _==choose(member(output,item),encode_words(output),
   IndexedWords{output:buffer(output).push(item),seen:key_index(output).set(item,true)})
   by cases member(output,item) {
    true=>normalize;
    false=>calc {
     _==IndexedWords{output:buffer(output).push(item),seen:key_index(output.concat([item]))} by normalize;
     ==IndexedWords{output:buffer(output).push(item),seen:key_index(output).set(item,true)}
      by congruence(normalize,use index_append_one(output,item));
     ==_ by normalize;
    };
   };
  ==_ by symmetry(use indexed_step_encoded(item,output));
 };
}
law ordered_dedup(xs:List<u32>,initial:List<u32>) {
 encode_words(foldl(xs,initial,fn(item,acc)=>dedup_step(item,acc)))==foldl(xs,encode_words(initial),fn(item,acc)=>indexed_step(item,acc));
 proof by use foldl_encoding<u32,List<u32>,IndexedWords>(xs,initial,fn(xs)=>encode_words(xs),fn(item,acc)=>dedup_step(item,acc),fn(item,acc)=>indexed_step(item,acc))
  assuming(use encoded_dedup_step(__assumed_item,__assumed_state));
}
law dedup_indexed(xs:List<u32>) {
 foldl(xs,empty_words(),fn(item,acc)=>dedup_step(item,acc))
 ==foldl(xs,encode_words(empty_words()),fn(item,acc)=>indexed_step(item,acc)).output.freeze();
 proof by calc {
  _==encode_words(foldl(xs,empty_words(),fn(item,acc)=>dedup_step(item,acc))).output.freeze() by normalize;
  ==_ by congruence(congruence(use ordered_dedup(xs,empty_words())));
 };
}

law membership_left(xs:List<u32>,key:u32) {
 foldl(xs,false,fn(item,found)=>found||key==item)==member(xs,key);
 proof by calc {
  _==(member(xs,key)||false) by use foldl_any<u32>(xs,false,fn(item)=>key==item);
  ==_ by cases member(xs,key) {true=>normalize;false=>normalize;};
 };
}

law membership_left_reversed(xs:List<u32>,key:u32) {
 foldl(xs,false,fn(item,found)=>found||item==key)==member(xs,key);
 proof by calc {
  _==(foldr(xs,false,fn(item,found)=>item==key||found)||false)
   by use foldl_any<u32>(xs,false,fn(item)=>item==key);
  ==(foldr(xs,false,fn(item,found)=>key==item||found)||false)
   by congruence(congruence(normalize,normalize,congruence(congruence(congruence(order(key,__congruence) then normalize,normalize)))),normalize);
  ==_ by cases member(xs,key) {true=>normalize;false=>normalize;};
 };
}

// Existing accumulator contents, including duplicates, are preserved exactly.
// The index only avoids appending a new item already present in that output.
law dedup_indexed_from(xs:List<u32>,initial:List<u32>) {
 foldl(xs,initial,fn(item,acc)=>dedup_step(item,acc))
 ==foldl(xs,encode_words(initial),fn(item,acc)=>indexed_step(item,acc)).output.freeze();
 proof by calc {
  _==encode_words(foldl(xs,initial,fn(item,acc)=>dedup_step(item,acc))).output.freeze() by normalize;
  ==_ by congruence(congruence(use ordered_dedup(xs,initial)));
 };
}

// Structural singleton identity agrees with scalar equality for word keys.
// This does not extend the alternative to floating-point scalar equality.
law membership_structural(xs:List<u32>,key:u32) {
 foldr(xs,false,fn(item,found)=>[item]==[key]||found)==member(xs,key);
 proof by calc {
  _==foldr(xs,false,fn(item,found)=>key==item||found)
   by congruence(normalize,normalize,
    congruence(congruence(congruence(order(key,__congruence) then normalize,normalize))));
  ==_ by normalize;
 };
}
