module ink.knowledge.map_algebra;

law map_overwrite_bool<V>(m:Map<Bool,V>,a:Bool,x:V,y:V) {
 
 m.set(a,x).set(a,y)==m.set(a,y);
 proof by provided;
}

law map_remove_twice_bool<V>(m:Map<Bool,V>,a:Bool) {
 
 m.remove(a).remove(a)==m.remove(a);
 proof by provided;
}

law map_remove_after_set_bool<V>(m:Map<Bool,V>,a:Bool,x:V) {
 
 m.set(a,x).remove(a)==m.remove(a);
 proof by provided;
}

law map_same_value_updates_bool<V>(m:Map<Bool,V>,a:Bool,b:Bool,x:V) {
 
 m.set(a,x).set(b,x)==m.set(b,x).set(a,x);
 proof by provided;
}

law map_overwrite_u32<V>(m:Map<u32,V>,a:u32,x:V,y:V) {
 
 m.set(a,x).set(a,y)==m.set(a,y);
 proof by provided;
}

law map_remove_twice_u32<V>(m:Map<u32,V>,a:u32) {
 
 m.remove(a).remove(a)==m.remove(a);
 proof by provided;
}

law map_remove_after_set_u32<V>(m:Map<u32,V>,a:u32,x:V) {
 
 m.set(a,x).remove(a)==m.remove(a);
 proof by provided;
}

law map_same_value_updates_u32<V>(m:Map<u32,V>,a:u32,b:u32,x:V) {
 
 m.set(a,x).set(b,x)==m.set(b,x).set(a,x);
 proof by provided;
}

law map_distinct_updates_u32<V>(m:Map<u32,V>,a:u32,b:u32,x:V,y:V) {
 requires distinct: a!=b;
 m.set(a,x).set(b,y)==m.set(b,y).set(a,x);
 proof by provided;
}

law map_overwrite_u64<V>(m:Map<u64,V>,a:u64,x:V,y:V) {
 
 m.set(a,x).set(a,y)==m.set(a,y);
 proof by provided;
}

law map_remove_twice_u64<V>(m:Map<u64,V>,a:u64) {
 
 m.remove(a).remove(a)==m.remove(a);
 proof by provided;
}

law map_remove_after_set_u64<V>(m:Map<u64,V>,a:u64,x:V) {
 
 m.set(a,x).remove(a)==m.remove(a);
 proof by provided;
}

law map_same_value_updates_u64<V>(m:Map<u64,V>,a:u64,b:u64,x:V) {
 
 m.set(a,x).set(b,x)==m.set(b,x).set(a,x);
 proof by provided;
}

law map_distinct_updates_u64<V>(m:Map<u64,V>,a:u64,b:u64,x:V,y:V) {
 requires distinct: a!=b;
 m.set(a,x).set(b,y)==m.set(b,y).set(a,x);
 proof by provided;
}

law map_overwrite_i32<V>(m:Map<i32,V>,a:i32,x:V,y:V) {
 
 m.set(a,x).set(a,y)==m.set(a,y);
 proof by provided;
}

law map_remove_twice_i32<V>(m:Map<i32,V>,a:i32) {
 
 m.remove(a).remove(a)==m.remove(a);
 proof by provided;
}

law map_remove_after_set_i32<V>(m:Map<i32,V>,a:i32,x:V) {
 
 m.set(a,x).remove(a)==m.remove(a);
 proof by provided;
}

law map_same_value_updates_i32<V>(m:Map<i32,V>,a:i32,b:i32,x:V) {
 
 m.set(a,x).set(b,x)==m.set(b,x).set(a,x);
 proof by provided;
}

law map_distinct_updates_i32<V>(m:Map<i32,V>,a:i32,b:i32,x:V,y:V) {
 requires distinct: a!=b;
 m.set(a,x).set(b,y)==m.set(b,y).set(a,x);
 proof by provided;
}
