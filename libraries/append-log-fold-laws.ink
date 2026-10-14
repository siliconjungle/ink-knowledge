module ink.knowledge.append_log_fold_laws;
// An append-only logical log can maintain a derived replay state incrementally.
// The step remains arbitrary: no commutativity or CRDT law is assumed.
law append_replay<A,S>(history:List<A>,incoming:List<A>,initial:S,step:fn(A,S)->S){
 foldl(history.concat(incoming),initial,step)==foldl(incoming,foldl(history,initial,step),step);
 proof by induction history generalizing(initial){
  nil=>normalize;
  cons(head,tail)=>ih(initial=step(head,initial));
 };
}
