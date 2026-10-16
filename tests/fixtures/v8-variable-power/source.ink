module variable_power_guards;
record Input {x:u32,y:u32,default:u32,}
fn slow(x:u32)->u32{return repeat(1000,x,fn(i)=>fn(a)=>a);}
pub fn samples(rows:List<Input>)->List<u32>{return rows.map(fn(r)=>rem_or(r.x,r.y,r.default));}
pub fn once(x:u32)->u32{return slow(x);}
pub fn strict_x(x:u32,y:u32)->u32{return rem_or(slow(x),y,73);}
pub fn strict_y(x:u32,y:u32)->u32{return rem_or(x,slow(y),73);}
pub fn lazy_default(x:u32,y:u32)->u32{return rem_or(x,y,slow(73));}
