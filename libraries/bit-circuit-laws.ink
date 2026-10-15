module ink.knowledge.bit_circuit_laws;
// Scalar components for packed circuits. The database admits these only after
// independently replaying source-bound RUP proofs. No hardware or model premise.
law disjoint_union_is_addition(a:u32,b:u32){
 requires disjoint: (a & b)==0;
 (a+b)==(a | b);
 proof by provided;
}
law bit_gate(value:u32,bit:u32){
 requires exact_bit: bit<=1;
 (((value ^ value)-bit) & value)==choose(bit==1,value,0);
 proof by provided;
}
law shift_and_union(a:u32,b:u32,mask:u32){
 (((wrapping_shl(a | b,1)) | 1) & mask)
 ==(((wrapping_shl(a,1) | 1) & mask) | ((wrapping_shl(b,1) | 1) & mask));
 proof by provided;
}
law shift_and_restart(mask:u32){
 ((wrapping_shl(mask & 0,1) | 1) & mask)==(mask & 1);
 proof by provided;
}
law octet_lane0(a:u32,b:u32,c:u32,d:u32){
 (((a & 255) | wrapping_shl(b & 255,8) | wrapping_shl(c & 255,16) | wrapping_shl(d & 255,24)) & 255)==(a & 255);
 proof by provided;
}
law octet_lane1(a:u32,b:u32,c:u32,d:u32){
 (wrapping_shr((a & 255) | wrapping_shl(b & 255,8) | wrapping_shl(c & 255,16) | wrapping_shl(d & 255,24),8) & 255)==(b & 255);
 proof by provided;
}
law octet_lane2(a:u32,b:u32,c:u32,d:u32){
 (wrapping_shr((a & 255) | wrapping_shl(b & 255,8) | wrapping_shl(c & 255,16) | wrapping_shl(d & 255,24),16) & 255)==(c & 255);
 proof by provided;
}
law octet_lane3(a:u32,b:u32,c:u32,d:u32){
 (wrapping_shr((a & 255) | wrapping_shl(b & 255,8) | wrapping_shl(c & 255,16) | wrapping_shl(d & 255,24),24) & 255)==(d & 255);
 proof by provided;
}
