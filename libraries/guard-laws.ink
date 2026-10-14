module ink.knowledge.guard_laws;
// Pure observations can reuse the result of a dominating identical guard.
// Source applicability and affine ownership still require checked replay.
law true_guard<S>(guard:Bool,first:S,second:S,third:S){
 choose(guard,choose(guard,first,second),third)==choose(guard,first,third);
 proof by cases guard {true=>normalize;false=>normalize;};
}
law false_guard<S>(guard:Bool,first:S,second:S,third:S){
 choose(guard,first,choose(guard,second,third))==choose(guard,first,third);
 proof by cases guard {true=>normalize;false=>normalize;};
}
