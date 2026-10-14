module ink.knowledge.early_exit_laws;
// An arbitrary state machine that stops after its first step needs no loop.
// Every application must discharge both stopping premises.
law single_step<S>(count:u32,state:S,stop:fn(S)->Bool,step:fn(u32,S)->S){
 requires running: stop(state)==false;
 requires finished: stop(step(0,state))==true;
 repeat_until(count,state,stop,step)==choose(count==0,state,step(0,state));
 proof by provided;
}
