module ink.knowledge.word_radix_laws;
// Scalar obligations used by packed unsigned integer streams. Certificates
// are supplied externally and checked against these exact source equations.
law radix7_roundtrip(value:u64){
 ((value & 127)
 | wrapping_shl(wrapping_shr(value,7) & 127,7)
 | wrapping_shl(wrapping_shr(value,14) & 127,14)
 | wrapping_shl(wrapping_shr(value,21) & 127,21)
 | wrapping_shl(wrapping_shr(value,28) & 127,28)
 | wrapping_shl(wrapping_shr(value,35) & 127,35)
 | wrapping_shl(wrapping_shr(value,42) & 127,42)
 | wrapping_shl(wrapping_shr(value,49) & 127,49)
 | wrapping_shl(wrapping_shr(value,56) & 127,56)
 | wrapping_shl(wrapping_shr(value,63) & 127,63))
 == value;
 proof by provided;
}
law octet_roundtrip(value:u32){
 ((value & 255)
 | wrapping_shl(wrapping_shr(value,8) & 255,8)
 | wrapping_shl(wrapping_shr(value,16) & 255,16)
 | wrapping_shl(wrapping_shr(value,24) & 255,24))
 == value;
 proof by provided;
}
law xor_delta_roundtrip(value:u64,previous:u64){
 ((value ^ previous) ^ previous) == value;
 proof by provided;
}
law position_delta_roundtrip(value:u32,previous:u32){
 ((value ^ previous) ^ previous) == value;
 proof by provided;
}
