module successor_bound_laws;
law candidate_dominates(key:u64,candidate:u64,previous:u64,empty:Bool){
 requires strict_bound: empty || candidate<previous;
 ((candidate>=key && (empty || candidate<previous)))==(candidate>=key);
 proof by provided;
}
law ordered_descendant(key:u64,candidate:u64,previous:u64){
 requires goes_left: key<=candidate;
 requires prior_bound: candidate<previous;
 (key<previous)==true;
 proof by provided;
}
