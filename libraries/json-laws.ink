module ink.knowledge.json_laws;
// General reusable object-list laws. These are external authoring source;
// JSON library calls elaborate to the same ordinary list and record meanings.
law lookup_after_put<A>(xs:List<A>,value:A,same:fn(A)->Bool,empty:Option<A>) {
 requires same(value);
 foldr([value].concat(xs.filter(fn(row)=>!same(row))),empty,fn(row,rest)=>choose(same(row),Some(row),rest)) == Some(value);
 proof by normalize;
}
law projection_idempotent<A>(xs:List<A>,keep:fn(A)->Bool) {
 xs.filter(keep).filter(keep) == xs.filter(keep);
 proof by induction xs {
  nil=>normalize;
  cons(h,t)=>cases keep(h) {true=>normalize;false=>normalize;};
 };
}
law project_map_fusion<A,B>(xs:List<A>,keep:fn(A)->Bool,convert:fn(A)->B) {
 xs.filter(keep).map(convert) == foldr(xs,[],fn(row,rest)=>choose(keep(row),[convert(row)].concat(rest),rest));
 proof by induction xs {
  nil=>normalize;
  cons(h,t)=>cases keep(h) {true=>normalize;false=>normalize;};
 };
}

law lookup_empty<A>(xs:List<A>,matches:fn(A)->Bool,empty:Option<A>) {
 requires xs==[];
 foldr(xs,empty,fn(row,rest)=>choose(matches(row),Some(row),rest)) == empty;
 proof by normalize;
}

// Concrete instances are searchable executable-domain laws, with their
// abstract premises discharged by ordinary equality computation.
law lookup_string_put(xs:List<String>,key:String,empty:Option<String>) {
 foldr([key].concat(xs.filter(fn(row)=>row!=key)),empty,fn(row,rest)=>choose(row==key,Some(row),rest)) == Some(key);
 proof by use lookup_after_put(xs,key,fn(row)=>row==key,empty);
}
law projection_string_idempotent(xs:List<String>,keep:fn(String)->Bool) {
 xs.filter(keep).filter(keep) == xs.filter(keep);
 proof by use projection_idempotent(xs,keep);
}
