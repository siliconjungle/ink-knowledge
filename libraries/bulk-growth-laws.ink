module ink.knowledge.bulk_growth_laws;
law appended_fill<T>(data:Buffer<T>,count:u32,value:T){
 data.append(buffer_fill(count,value)).freeze()==data.freeze().concat(buffer_fill(count,value).freeze());
 proof by normalize;
}
law right_empty<T>(values:List<T>){values.concat([])==values;proof by induction values;}
law zero_growth<T>(data:Buffer<T>,value:T){
 data.append(buffer_fill(0,value)).freeze()==data.freeze();
 proof by calc{_==data.freeze().concat([]) by normalize;==_ by use right_empty<T>(data.freeze());};
}
