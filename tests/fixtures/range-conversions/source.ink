module range_conversions;
fn guarded(x:u64)->u64 {return choose(x<=4294967295,word_widen_u32_to_u64(word_narrow_u64_to_u32(x)),x);}
fn opposite(x:u64)->u64 {return choose(x<=4294967295,x,word_widen_u32_to_u64(word_narrow_u64_to_u32(x)));}
fn relational(x:u64,upper:u64)->u64 {return choose(x<upper && upper<=4294967296,word_widen_u32_to_u64(word_narrow_u64_to_u32(x)),x);}
fn wrapped(x:u64)->u64 {return choose(x+1<=4294967295,word_widen_u32_to_u64(word_narrow_u64_to_u32(x+1)),x+1);}
fn wrong_input(x:u64)->u64 {return choose(x+1<=4294967295,word_widen_u32_to_u64(word_narrow_u64_to_u32(x)),x);}
fn unchanged(x:u64)->u64 {return word_widen_u32_to_u64(word_narrow_u64_to_u32(x));}
fn small(x:u32)->u32 {return word_narrow_u64_to_u32(word_widen_u32_to_u64(x));}
