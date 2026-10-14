module ink.knowledge.chunk_laws;

law foldl_append<A,S>(xs:List<A>,ys:List<A>,state:S,step:fn(A,S)->S) {
    foldl(xs.concat(ys),state,step) == foldl(ys,foldl(xs,state,step),step);
    proof by induction xs generalizing(state) {
        nil => normalize;
        cons(head,tail) => ih(state=step(head,state));
    };
}

law flatten_fold<A,S>(chunks:List<List<A>>,state:S,step:fn(A,S)->S) {
    foldl(foldr(chunks,chunks.at_or(0,[]).take(0),fn(chunk,rest)=>chunk.concat(rest)),state,step)
        == foldl(chunks,state,fn(chunk,current)=>foldl(chunk,current,step));
    proof by induction chunks generalizing(state) {
        nil => normalize;
        cons(head,tail) => calc {
            _ == foldl(foldr(tail,tail.at_or(0,[]).take(0),fn(chunk,rest)=>chunk.concat(rest)),foldl(head,state,step),step)
                by use foldl_append<A,S>(head,foldr(tail,tail.at_or(0,[]).take(0),fn(chunk,rest)=>chunk.concat(rest)),state,step);
              == _ by ih(state=foldl(head,state,step));
        };
    };
}

law foldl_state<A,S>(xs:List<A>,first:S,second:S,step:fn(A,S)->S) {
    requires equal: first == second;
    foldl(xs,first,step) == foldl(xs,second,step);
}

law foldl_steps<A,S>(xs:List<A>,state:S,first:fn(A,S)->S,second:fn(A,S)->S) {
    assume agrees(item:A,current:S): first(item,current) == second(item,current);
    foldl(xs,state,first) == foldl(xs,state,second);
    proof by induction xs generalizing(state) {
        nil => normalize;
        cons(head,tail) => calc {
            _ == foldl(tail,first(head,state),second)
                by ih(state=first(head,state));
              == _ by use foldl_state<A,S>(tail,first(head,state),second(head,state),second)
                requires(assumption agrees(head,state));
        };
    };
}

law bulk_chunks<A,S>(chunks:List<List<A>>,state:S,step:fn(A,S)->S,bulk:fn(List<A>,S)->S) {
    assume preserves(chunk:List<A>,current:S): foldl(chunk,current,step) == bulk(chunk,current);
    foldl(foldr(chunks,chunks.at_or(0,[]).take(0),fn(chunk,rest)=>chunk.concat(rest)),state,step) == foldl(chunks,state,bulk);
    proof by calc {
        _ == foldl(chunks,state,fn(chunk,current)=>foldl(chunk,current,step))
            by use flatten_fold<A,S>(chunks,state,step);
          == _ by use foldl_steps<List<A>,S>(chunks,state,fn(chunk,current)=>foldl(chunk,current,step),bulk)
            assuming(assumption preserves(__assumed_item,__assumed_current));
    };
}

// Concrete preservation instance: all arithmetic retains u64 wrapping.
law sum_chunk(chunk:List<u64>,current:u64) {
    foldl(chunk,current,fn(value,acc)=>acc+value) == current+sum(chunk);
    proof by induction chunk generalizing(current) {
        nil => normalize;
        cons(head,tail) => calc {
            _ == current+head+sum(tail) by ih(current=current+head);
              == _ by normalize;
        };
    };
}

law bulk_sum(chunks:List<List<u64>>,state:u64) {
    foldl(foldr(chunks,chunks.at_or(0,[]).take(0),fn(chunk,rest)=>chunk.concat(rest)),state,fn(value,acc)=>acc+value)
        == foldl(chunks,state,fn(chunk,acc)=>acc+sum(chunk));
    proof by use bulk_chunks<u64,u64>(chunks,state,fn(value,acc)=>acc+value,fn(chunk,acc)=>acc+sum(chunk))
        assuming(use sum_chunk(__assumed_chunk,__assumed_current));
}
