module ink.knowledge.word_equality_laws;
law zero_from_test(value:u32){
 requires zero_test: (value==0)==true;
 value==0;
 proof by provided;
}
