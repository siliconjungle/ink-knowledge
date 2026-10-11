module field_snapshot_schema;
record Row{id:u32,x:u32,y:u32,score:u32,flags:u32,}
fn identity(row:Row)->Row{return row;}
