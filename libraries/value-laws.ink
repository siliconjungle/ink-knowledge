module ink.knowledge.value_laws;
// External authoring source. These declarations are not executable application
// syntax and cannot silently enable a rewrite. Their evidence is checked.
rewrite exact_double(x:Int) {
    from x+x;
    to x*2;
    proof by normalize;
}
rewrite exact_difference_of_squares(x:Int) {
    from (x+1)*(x-1);
    to x*x-1;
    proof by normalize;
}
rewrite exact_cancellation(x:Int,y:Int) {
    from (x-y)+y;
    to x;
    proof by normalize;
}
