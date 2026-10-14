module ink.knowledge.drop_composition;
law decrement_room(a:u32,b:u32){
 requires positive:!(a==0);
 requires room:a<=4294967295-b;
 (a-1<=4294967295-b)==true;
 proof by provided;
}
law positive_total(a:u32,b:u32){
 requires positive:!(a==0);
 requires room:a<=4294967295-b;
 (a+b==0)==false;
 proof by provided;
}
