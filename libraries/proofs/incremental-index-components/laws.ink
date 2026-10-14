module minimum_preservation;
law unchanged_word(old:u64,value:u64){
 requires same: old==value;
 value==old;
 proof by provided;
}
law suffix_count(position:u32,count:u32){
 requires valid_position: position<=count;
 requires has_room: count<4294967295;
 (position+(count+1-position))==(count+1);
 proof by provided;
}
