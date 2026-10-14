module ink.knowledge.unchanging_read_laws;
// Reuse requires preservation of the entire input state, not merely equal text.
law repeat_read<S,R>(state:S,read:fn(S)->R,recover:fn(R)->S){
 assume preserved(current:S): recover(read(current))==current;
 read(recover(read(state)))==read(state);
 proof by congruence(normalize,assumption preserved(state));
}
