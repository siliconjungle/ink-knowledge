module ink.knowledge.record_frame_laws;
// Concrete regression instances of the declared record meanings. General
// source helper projection still needs its own exact source equality.
record Row{key:u32,payload:List<u32>,}
record Frame{data:Buffer<u32>,tag:u64,}
law row_identity(row:Row){Row{payload:row.payload,key:row.key}==row;proof by normalize;}
law frame_identity(frame:Frame){Frame{data:frame.data,tag:frame.tag}==frame;proof by normalize;}
