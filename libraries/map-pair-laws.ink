module ink.knowledge.map_pair_laws;
record Pair{key:u64,value:Bool,}
law decode_lookup(entries:List<Pair>,initial:Map<u64,Bool>,key:u64,fallback:Bool){
 foldl(entries,initial,fn(entry,map)=>map.set(entry.key,entry.value)).get_or(key,fallback)
  ==foldl(entries,initial.get_or(key,fallback),fn(entry,value)=>choose(key==entry.key,entry.value,value));
 proof by induction entries generalizing(initial){
  nil=>normalize;
  cons(head,tail)=>calc{
   _==foldl(tail,initial.set(head.key,head.value),fn(entry,map)=>map.set(entry.key,entry.value)).get_or(key,fallback) by normalize;
    ==foldl(tail,initial.set(head.key,head.value).get_or(key,fallback),fn(entry,value)=>choose(key==entry.key,entry.value,value)) by ih(initial=initial.set(head.key,head.value));
    ==_ by normalize;
  };
 };
}
