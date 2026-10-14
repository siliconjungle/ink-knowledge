module ink.knowledge.bulk_range_laws;
law zero_copy<A>(xs:List<A>,source:u32,destination:u32){buffer(xs).copy_within(source,destination,0).freeze()==xs;proof by normalize;}
law zero_fill<A>(xs:List<A>,start:u32,value:A){buffer(xs).fill_range(start,0,value).freeze()==xs;proof by normalize;}
