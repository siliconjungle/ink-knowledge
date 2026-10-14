module ink.knowledge.chunked_sequence;

// Logical decoding and direct execution over ordered chunks. Application
// algorithms and checked alternatives supply their own bulk transition.
fn flatten<T>(chunks:List<List<T>>)->List<T> {
    return foldr(chunks,[],fn(chunk,rest)=>chunk.concat(rest));
}
fn execute<A,S>(chunks:List<List<A>>,state:S,step:fn(A,S)->S)->S {
    return foldl(chunks,state,fn(chunk,current)=>foldl(chunk,current,step));
}
fn execute_bulk<A,S>(chunks:List<List<A>>,state:S,bulk:fn(List<A>,S)->S)->S {
    return foldl(chunks,state,bulk);
}
